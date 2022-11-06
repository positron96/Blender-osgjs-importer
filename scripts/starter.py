import newGameLib
from newGameLib import *
import Blender	

import json
import logging
import copy

logger = logging.getLogger(__file__)
logger.setLevel(logging.INFO)
logging.basicConfig(level=logging.INFO)

################################################
#BINDPOSE = 0
BINDPOSE = 1
################################################
	

class Importer:

	def __init__(self, filename):
		self.filename = filename

		self.obj2bone = {}
		self.model = Model(self.filename)
		self.skeleton = Skeleton()
		self.skeleton.ARMATURESPACE = True
		self.bindskeleton = Skeleton()
		self.bindskeleton.NICE = True
		self.bindskeleton.ARMATURESPACE = True

		self.state_uid_to_mtl_uid = {}
		self.materials = {}
		
		self.firstmatrix = Matrix4x4([1,0,0,0, 0,0,1,0, 0,-1,0,0, 0,0,0,1])

		self.parse_osgjs()
	
	def find_path(self, filename):
		dirname = os.path.dirname(self.filename)
		path = os.path.join(dirname, filename)
		if not os.path.exists(path): path = os.path.join(dirname, 'model_file.bin')
		if not os.path.exists(path): path = os.path.join(dirname, 'model_file.bin.gz.txt')
		if not os.path.exists(path):
			raise Exception('File not found: ' + filename)
		return path
	
	def decode_varint(self, reader, offset, size, type):
		reader.seek(offset)
		ret = [0]*size
		pos = 0
		while(pos != size):
			shift = 0
			result = 0
			while True:
				byte = reader.B(1)[0]
				result |= (byte & 127) << shift
				shift += 7
				if not (byte & 0x80):break			
			ret[pos] = result		
			pos += 1
		if type[0] != 'U':
			l = 0
			while(l<size):
				h = ret[l]
				ret[l] = h>>1 ^ -(1&h)
				l += 1
		return ret

			
	def decode_delta(self, t, e):
		i = e|0
		n = len(t)
		if i>=len(t): 
			r = None
		else: 
			r = t[i]
		a = i + 1
		while(a<n):
			s = t[a]
			r = t[a] = r + (s>>1^-(1&s))
			a += 1
		return t	


	def decode_implicit(self, input, n):
		IMPLICIT_HEADER_LENGTH = 3
		IMPLICIT_HEADER_MASK_LENGTH = 1
		IMPLICIT_HEADER_PRIMITIVE_LENGTH = 0
		IMPLICIT_HEADER_EXPECTED_INDEX = 2
		highWatermark = 2
		
		t = input
		e = [0]*t[IMPLICIT_HEADER_PRIMITIVE_LENGTH]
		a = t[IMPLICIT_HEADER_EXPECTED_INDEX]
		s = t[IMPLICIT_HEADER_MASK_LENGTH]
		o = t[IMPLICIT_HEADER_LENGTH: s + IMPLICIT_HEADER_LENGTH]
		r = highWatermark
		u = 32 * s - len(e)
		l = 1<<31
		h = 0	
		while(h<s):
			c = o[h]
			d = 32
			p = h * d
			if h == s - 1: f = u
			else: f = 0
			g1 = f
			while(g1<d):
				if c&l>>g1:
					e[p] = t[n]
					n += 1	
				else:
					if r:
						e[p] = a
					else:
						e[p] = a
						a += 1			
				g1 += 1
				p += 1
			h += 1
		return e
	
	
	def decode_watermark(self, t, e, magic):
		r = len(t)
		a = 0
		while(a<r):
			s = magic - t[a]
			e[a] = s
			if magic<=s: magic = s + 1
			a += 1
		return e, magic

		
	def decode_indices(self, itemsize, size, offset, type, reader, mode, magic):
		if type != "Uint8Array":
			bytes = self.decode_varint(reader, offset, size * itemsize, type)
		else:
			reader.seek(offset)
			bytes = list(reader.B(size * itemsize))		
		#write(dbg, [magic],0)
		#write(dbg, bytes, 0)		
		
		IMPLICIT_HEADER_LENGTH = 3
		IMPLICIT_HEADER_MASK_LENGTH = 1
		IMPLICIT_HEADER_PRIMITIVE_LENGTH = 0
		IMPLICIT_HEADER_EXPECTED_INDEX = 2
		highWatermark = 2
			
		if mode == 'TRIANGLE_STRIP':
			k = IMPLICIT_HEADER_LENGTH + bytes[IMPLICIT_HEADER_MASK_LENGTH]
			bytes = self.decode_delta(bytes, k)	
			#write(dbg, [magic, k],0)	
			#write(dbg, bytes, 0)		
			bytes = self.decode_implicit(bytes, k)
			#write(dbg, [magic, k],0)	
			#write(dbg, bytes, 0)			
			bytes, magic = self.decode_watermark(bytes, bytes, magic)
			#write(dbg, [magic],0)	
			#write(dbg, bytes, 0)	
				
		elif mode == 'TRIANGLES':
			k = 0
			bytes = self.decode_delta(bytes, k)
			#write(dbg, [magic],0)	
			#write(dbg, bytes, 0)			
			bytes, magic = self.decode_watermark(bytes, bytes, magic)
			#write(dbg, [magic],0)	
			#write(dbg, bytes, 0)	

		return magic, bytes
	
	
	def decode_predict(self, indices, input, itemsize):	
		t = input	
		if len(indices)>0:
			t = input	
			e = itemsize
			i = indices	
			n = len(t)/e
			r = [0]*n
			a = len(i)-1
			r[i[0]] = 1
			r[i[1]] = 1
			r[i[2]] = 1	
			s = 2
			while(s<a):
				o = s - 2
				u = i[o]
				l = i[o + 1]
				h = i[o + 2]
				c = i[o + 3]
				if 1 != r[c]:
					r[c] = 1
					u *= e
					l *= e
					h *= e
					c *= e			
					d = 0
					while(d<e):
						t[c + d] = t[c + d]+t[l + d]+t[h + d]-t[u + d]
						d += 1
				s += 1
		return t

	def decode_quantize(self, input, s, a, itemsize):
		x = [0]*len(input)
		id = 0
		for r in range(len(input)/itemsize):
			for l in range(itemsize):
				x[id] = s[l]+input[id]*a[l]
				id += 1
		return x	

	def getSplitName(self, name, sep, which):
		a = None
		if sep in name:
			a = ''
			splits = name.split(sep)
			if which < 0:
				num = len(splits)+which - 1
			else:
				num = which
			if num < 0:
				a = name
			else:		
				if which < len(splits):			
					for m in range(num):
						a += splits[m]+sep
					a += splits[num]
				else:
					a = name		
		return a	
		

	def getAnimation(self, A,n):
		action = Action()
		action.ARMATURESPACE = True
		action.BONESORT = True
		action.skeleton = skeleton.name
		n += 4
		Channels = ys.get(A, '"Channels"')
		boneList = {}
		if Channels:
			values = ys.values(Channels[0].header, ':')
			Name = ys.getValue(values, '"Name"')
			action.name = Name
			write(dbg, [Name],n)
			
			for a in  Channels[0].children:
				write(dbg, ['Bone'],n)
				Vec3LerpChannel = ys.get(a, '"osgAnimation.Vec3LerpChannel"')
				bone = None
				if Vec3LerpChannel:
					KeyFrames = ys.get(a, '"KeyFrames"')
					if KeyFrames:
						values = ys.values(KeyFrames[0].header, ':')
						Name = ys.getValue(values, '"Name"')
						TargetName = ys.getValue(values, '"TargetName"','""')
						write(dbg, ['Vec3LerpChannel: ',Name, 'TargetName: ',TargetName],n + 4)
						name = getSplitName(TargetName, '_',-1)
						if Name == '"translate"':
							if name in obj2bone:
								name = obj2bone[name]
								if name not in boneList.keys():
									bone = ActionBone()
									action.boneList.append(bone)
									bone.name = name
									boneList[name] = bone
								bone = boneList[name]
							
							
							Key = ys.get(a, '"Key"')
							if Key:
								values = ys.values(Key[0].data, ':')
								ItemSize = ys.getValue(values, '"ItemSize"','i')						
								Float32Array = ys.get(Key[0],'"Float32Array"')
								if Float32Array:
									values = ys.values(Float32Array[0].data, ':')
									File = ys.getValue(values, '"File"')
									Size = ys.getValue(values, '"Size"')
									Offset = ys.getValue(values, '"Offset"')
									write(dbg, [File, 'Size: ',Size, 'Offset: ',Offset, 'ItemSize: ',ItemSize],n + 4)
									path = os.path.dirname(input.filename)+os.sep + File.split('"')[1].split('.gz')[0]
									if os.path.exists(path):
										file = open(path, 'rb')
										g = BinaryReader(file)
										g.seek(int(Offset))
										for m in range(int(Size)):
											value = g.f(ItemSize)
											write(dbg, value, n + 8)
											if bone:
												boneMatrix = skeleton.object.getData().bones[bone.name].matrix['ARMATURESPACE']
												bone.posKeyList.append(boneMatrix * VectorMatrix(value))
										file.close()
							
							Time = ys.get(a, '"Time"')
							if Time:
								values = ys.values(Time[0].data, ':')
								ItemSize = ys.getValue(values, '"ItemSize"','i')						
								Float32Array = ys.get(Time[0],'"Float32Array"')
								if Float32Array:
									values = ys.values(Float32Array[0].data, ':')
									File = ys.getValue(values, '"File"')
									Size = ys.getValue(values, '"Size"')
									Offset = ys.getValue(values, '"Offset"')
									write(dbg, [File, 'Size: ',Size, 'Offset: ',Offset, 'ItemSize: ',ItemSize],n + 4)
									path = os.path.dirname(input.filename)+os.sep + File.split('"')[1].split('.gz')[0]
									if os.path.exists(path):
										file = open(path, 'rb')
										g = BinaryReader(file)
										g.seek(int(Offset))
										for m in range(int(Size)):
											value = g.f(ItemSize)
											if ItemSize == 1: value = value[0]
											#write(dbg, [value],n + 8)
											if bone: bone.posFrameList.append(int(value * 33))
										file.close()
						
										
				Vec3LerpChannelCompressedPacked = ys.get(a, '"osgAnimation.Vec3LerpChannelCompressedPacked"')
				if Vec3LerpChannelCompressedPacked:
				
					atributes = {}
					UserDataContainer = ys.get(Vec3LerpChannelCompressedPacked[0],'"UserDataContainer"')
					if UserDataContainer:
						Values = ys.get(UserDataContainer[0],'"Values"')
						if Values:
							for child in Values[0].children:
								values = ys.values(child.data, ':')
								Name = ys.getValue(values, '"Name"')
								Value = ys.getValue(values, '"Value"','"f"')
								#write(dbg, [Name, Value],n + 4)
								atributes[Name] = Value
					
					KeyFrames = ys.get(a, '"KeyFrames"')
					if KeyFrames:
						values = ys.values(KeyFrames[0].header, ':')
						Name = ys.getValue(values, '"Name"')
						TargetName = ys.getValue(values, '"TargetName"','""')
						write(dbg, ['Vec3LerpChannelCompressedPacked: ',Name, 'TargetName: ',TargetName],n + 4)
						name = getSplitName(TargetName, '_',-1)
						if Name == '"translate"':
							if name in obj2bone:
								name = obj2bone[name]
								if name not in boneList.keys():
									bone = ActionBone()
									action.boneList.append(bone)
									bone.name = name
									boneList[name] = bone
								bone = boneList[name]
							
							Key = ys.get(a, '"Key"')
							if Key:
								values = ys.values(Key[0].data, ':')
								ItemSize = int(ys.getValue(values, '"ItemSize"'))						
								Uint16Array = ys.get(Key[0],'"Uint16Array"')
								type = "Uint16Array"
								if Uint16Array:
									values = ys.values(Uint16Array[0].data, ':')
									File = ys.getValue(values, '"File"')
									Size = int(ys.getValue(values, '"Size"'))
									Offset = int(ys.getValue(values, '"Offset"'))
									Encoding = ys.getValue(values, '"Encoding"')
									write(dbg, [File, 'Size: ',Size, 'Offset: ',Offset, 'Encoding: ',Encoding, 'ItemSize: ',ItemSize],n + 4)
									path = os.path.dirname(input.filename)+os.sep + File.split('"')[1].split('.gz')[0]
									if os.path.exists(path):
										file = open(path, 'rb')
										g = BinaryReader(file)
										
										list = decode_varint(g, Offset, Size * ItemSize, type)
										list1 = etap1(list, ItemSize)
										out = etap2(list1, ItemSize, atributes)
										list2 = [atributes['"ox"'],atributes['"oy"'],atributes['"oz"']]
										list2.extend(out)
										list3 = etap3(list2, ItemSize)
										for m in range(Size + 1):
											value = list3[m * 3: m * 3 + 3]
											write(dbg, value, n + 8)
											if bone:
												boneMatrix = skeleton.object.getData().bones[bone.name].matrix['ARMATURESPACE']
												bone.posKeyList.append(boneMatrix * VectorMatrix(value))
										file.close()
							
							Time = ys.get(a, '"Time"')
							if Time:
								values = ys.values(Time[0].data, ':')
								ItemSize = ys.getValue(values, '"ItemSize"','i')						
								Float32Array = ys.get(Time[0],'"Float32Array"')
								if Float32Array:
									values = ys.values(Float32Array[0].data, ':')
									File = ys.getValue(values, '"File"')
									Size = ys.getValue(values, '"Size"','i')
									Offset = ys.getValue(values, '"Offset"','i')
									write(dbg, [File, 'Size: ',Size, 'Offset: ',Offset, 'ItemSize: ',ItemSize],n + 4)
									path = os.path.dirname(input.filename)+os.sep + File.split('"')[1].split('.gz')[0]
									if os.path.exists(path):
										file = open(path, 'rb')
										g = BinaryReader(file)
										g.seek(int(Offset))
										list = g.f(Size * ItemSize)
										list1 = etap1(list, ItemSize)
										#out = etap2(list1, ItemSize, atributes)
										list2 = [atributes['"ot"']]
										list2.extend(list1)
										list3 = etap3(list2, ItemSize)
										#write(dbg, list3, 0)
										for m in range(Size + 1):
											value = list3[m]
											if bone: bone.posFrameList.append(int(value * 33))
										file.close()
						
						
						
				QuatSlerpChannel = ys.get(a, '"osgAnimation.QuatSlerpChannel"')
				if QuatSlerpChannel:
					KeyFrames = ys.get(a, '"KeyFrames"')
					if KeyFrames:
						values = ys.values(KeyFrames[0].header, ':')
						Name = ys.getValue(values, '"Name"')
						TargetName = ys.getValue(values, '"TargetName"','""')
						write(dbg, ['QuatSlerpChannel: ',Name, 'TargetName: ',TargetName],n + 4)
						name = getSplitName(TargetName, '_',-1)
						if name in obj2bone:
							name = obj2bone[name]
							if name not in boneList.keys():
								bone = ActionBone()
								action.boneList.append(bone)
								bone.name = name
								boneList[name] = bone
							bone = boneList[name]
						
						
						
						Key = ys.get(a, '"Key"')
						if Key:
							values = ys.values(Key[0].data, ':')
							ItemSize = ys.getValue(values, '"ItemSize"')						
							Float32Array = ys.get(Key[0],'"Float32Array"')
							if Float32Array:
								values = ys.values(Float32Array[0].data, ':')
								File = ys.getValue(values, '"File"')
								Size = ys.getValue(values, '"Size"')
								Offset = ys.getValue(values, '"Offset"')
								write(dbg, [File, 'Size: ',Size, 'Offset: ',Offset, 'ItemSize: ',ItemSize],n + 4)
								path = os.path.dirname(input.filename)+os.sep + File.split('"')[1].split('.gz')[0]
								if os.path.exists(path):
									file = open(path, 'rb')
									g = BinaryReader(file)
									g.seek(int(Offset))
									for m in range(int(Size)):
										value = g.f(4)
										value = Quaternion(value)
										if bone:
											boneMatrix = skeleton.object.getData().bones[bone.name].matrix['ARMATURESPACE']
											bone.rotKeyList.append(boneMatrix * QuatMatrix(value).resize4x4())
									file.close()
						
						Time = ys.get(a, '"Time"')
						if Time:
							values = ys.values(Time[0].data, ':')
							ItemSize = ys.getValue(values, '"ItemSize"','i')						
							Float32Array = ys.get(Time[0],'"Float32Array"')
							if Float32Array:
								values = ys.values(Float32Array[0].data, ':')
								File = ys.getValue(values, '"File"')
								Size = ys.getValue(values, '"Size"')
								Offset = ys.getValue(values, '"Offset"')
								write(dbg, [File, 'Size: ',Size, 'Offset: ',Offset, 'ItemSize: ',ItemSize],n + 4)
								path = os.path.dirname(input.filename)+os.sep + File.split('"')[1].split('.gz')[0]
								if os.path.exists(path):
									file = open(path, 'rb')
									g = BinaryReader(file)
									g.seek(int(Offset))
									for m in range(int(Size)):
										value = g.f(ItemSize)
										if ItemSize == 1: value = value[0]
										if bone: bone.rotFrameList.append(int(value * 33))
									file.close()
						
										
				QuatSlerpChannelCompressedPacked = ys.get(a, '"osgAnimation.QuatSlerpChannelCompressedPacked"')
				if QuatSlerpChannelCompressedPacked:
				
				
					atributes = {}
					UserDataContainer = ys.get(QuatSlerpChannelCompressedPacked[0],'"UserDataContainer"')
					if UserDataContainer:
						Values = ys.get(UserDataContainer[0],'"Values"')
						if Values:
							for child in Values[0].children:
								values = ys.values(child.data, ':')
								Name = ys.getValue(values, '"Name"')
								Value = ys.getValue(values, '"Value"','"f"')
								#write(dbg, [Name, Value],n + 4)
								atributes[Name] = Value
				
					KeyFrames = ys.get(a, '"KeyFrames"')
					if KeyFrames:
						values = ys.values(KeyFrames[0].header, ':')
						Name = ys.getValue(values, '"Name"')
						TargetName = ys.getValue(values, '"TargetName"','""')
						write(dbg, ['QuatSlerpChannelCompressedPacked: ',Name, 'TargetName: ',TargetName],n + 4)
						name = getSplitName(TargetName, '_',-1)
						if name in obj2bone:
							name = obj2bone[name]
							if name not in boneList.keys():
								bone = ActionBone()
								action.boneList.append(bone)
								bone.name = name
								boneList[name] = bone
							bone = boneList[name]
							
						Key = ys.get(a, '"Key"')
						if Key:
							values = ys.values(Key[0].data, ':')
							ItemSize = int(ys.getValue(values, '"ItemSize"'))						
							Uint16Array = ys.get(Key[0],'"Uint16Array"')
							type = "Uint16Array"
							if Uint16Array:
								values = ys.values(Uint16Array[0].data, ':')
								File = ys.getValue(values, '"File"')
								Size = int(ys.getValue(values, '"Size"'))
								Offset = int(ys.getValue(values, '"Offset"'))
								Encoding = ys.getValue(values, '"Encoding"')
								write(dbg, [File, 'Size: ',Size, 'Offset: ',Offset, 'Encoding: ',Encoding, 'ItemSize: ',ItemSize],n + 4)
								path = os.path.dirname(input.filename)+os.sep + File.split('"')[1].split('.gz')[0]
								if os.path.exists(path):
									file = open(path, 'rb')
									g = BinaryReader(file)
									
									list = decode_varint(g, Offset, Size * ItemSize, type)
									#write(dbg, list, 0)
									list1 = etap1(list, ItemSize)
									#write(dbg, list1, 0)
									
									list2 = int3float4(list1, atributes, ItemSize)								
									#write(dbg, list2, 0)
									list3 = [atributes['"ox"'],atributes['"oy"'],atributes['"oz"'],atributes['"ow"']]
									list3.extend(list2)
									list4 = etap4(list3)
									#write(dbg, list4, 0)
									
									for m in range(Size + 1):
										value = list4[m * 4: m * 4 + 4]									
										value = Quaternion(value)
										#write(dbg, value, n + 8)
										if bone:
											boneMatrix = skeleton.object.getData().bones[bone.name].matrix['ARMATURESPACE']
											##bone.rotKeyList.append((boneMatrix.rotationPart()*QuatMatrix(value)).resize4x4())
											bone.rotKeyList.append(boneMatrix * QuatMatrix(value).resize4x4())
									file.close()
						
						Time = ys.get(a, '"Time"')
						if Time:
							values = ys.values(Time[0].data, ':')
							ItemSize = ys.getValue(values, '"ItemSize"','i')						
							Float32Array = ys.get(Time[0],'"Float32Array"')
							if Float32Array:
								values = ys.values(Float32Array[0].data, ':')
								File = ys.getValue(values, '"File"')
								Size = ys.getValue(values, '"Size"','i')
								Offset = ys.getValue(values, '"Offset"','i')
								write(dbg, [File, 'Size: ',Size, 'Offset: ',Offset, 'ItemSize: ',ItemSize],n + 4)
								path = os.path.dirname(input.filename)+os.sep + File.split('"')[1].split('.gz')[0]
								if os.path.exists(path):
									file = open(path, 'rb')
									g = BinaryReader(file)
									g.seek(int(Offset))
									list = g.f(Size * ItemSize)
									list1 = etap1(list, ItemSize)
									#out = etap2(list1, ItemSize, atributes)
									list2 = [atributes['"ot"']]
									list2.extend(list1)
									list3 = etap3(list2, ItemSize)
									#write(dbg, list3, 0)
									for m in range(Size + 1):
										value = list2[m]
										if bone: bone.rotFrameList.append(int(value * 33))
									file.close()
					
				if bone:	
					logger.info("%s", (name, bone.name,))
					
		action.draw()
		action.setContext()	
					
	def process_primitive_set_list(self, primitive_set_list, n):
		mode = None
		self.magic = 0
		index_arr = []
		for child in primitive_set_list:
			_type, obj = next(iter(child.items()))
			mode = obj['Mode']
			logger.info('process_primitive_set_list %s %s', _type, mode)
			
			if mode != 'LINES':
				indices_obj = obj.get('Indices')
				if indices_obj:
					item_size = indices_obj['ItemSize']
					index_list, _ = self.load_array(indices_obj['Array'], item_size, mode, True, False)
					index_arr.append([index_list, mode])
			else:
				logger.info('process_primitive_set_list skipped LINES')
					
		return index_arr
								
	def load_array(self, arr_node, item_size, mode, is_index=False, no_varint=True):
		arr_type, arr_obj = next(iter(arr_node.items()))
			
		size = arr_obj['Size']
		offset = arr_obj['Offset']
		encoding = arr_obj['Encoding']

		#write(dbg, ['Array: ', arr_type, 'Size: ', size, 'Offset: ', offset, 'Encoding: ',encoding, 'magic: ', self.magic], 0)
		#logger.info('load_array: %s, size: %d, ofs %d, enc %s, magic %s, mode %s', arr_type, size, offset, encoding, self.magic, mode)

		path = self.find_path(arr_obj['File'])

		with open(path, 'rb') as f:
			reader = BinaryReader(f)
			if encoding == 'varint':
				if is_index:
					self.magic, array = self.decode_indices(item_size, size, offset, arr_type, reader, mode, self.magic)
				else:
					array = self.decode_varint(reader, offset, size*item_size, arr_type)
				return array, encoding					
			else:	
				if no_varint:			
					reader.seek(offset)
					if 'Int32' in arr_type:
						return reader.H(item_size * size), encoding
					elif 'Float32' in arr_type:
						fdata = reader.f(size * item_size)
						ret = []
						for m in range(size):
							ret.append(fdata[m*item_size: m*item_size + item_size])  
						if mode == 'TexCoord0':
							for f in ret:  # swap V
								f[1] = 1 - f[1]
						return ret, encoding
				
				
	def process_vertex_attrs(self, vertex_attrs, n):
		vertex_arr = []
		tex_arr = []
		
		vertex = vertex_attrs.get('Vertex')
		if vertex:		
			mode = 'Vertex'
			#logger.info('process_vertex_attrs: Vertex UID:%s', vertex.get('UniqueID'))
			if 'ItemSize' in vertex:
				item_size = vertex['ItemSize']	
				fdata, enc = self.load_array(vertex['Array'], item_size, mode)
				vertex_arr.append([fdata, enc, item_size])

		tex_coord0 = vertex_attrs.get('TexCoord0')
		if tex_coord0:
			mode = 'TexCoord0'
			#logger.info('process_vertex_attrs: TexCoord0 UID:%s', tex_coord0.get('UniqueID'))
			if 'ItemSize' in tex_coord0:
				item_size = tex_coord0['ItemSize']
				fdata, enc = self.load_array(tex_coord0['Array'], item_size, mode)
				tex_arr.append([fdata, enc, item_size])
										
		return vertex_arr, tex_arr							
				
	def getRigGeometry(self, parent, n):
		logger.info("%s", ('#'*50, 'RigGeometry',))
		n += 4
		BoneMap = [0]*1000
		bones = []
		weights = []
		mode = None
		indexArray = []
		vertexArray = []
		texArray = []
		atributes = {}
		for child in parent.children:
			if "BoneMap" in child.header:
				write(dbg, ['BoneMap'],n)
				values = ys.values(child.data, ':')
				#logger.info("%s", (values,))
				for value in values:
					id = ys.getValue(values, value, 'i')
					name = value.split('"')[1]
					BoneMap[id] = getSplitName(name, '_',-1)
			if "SourceGeometry" in child.header:
				values = ys.values(child.data, ':')
				PrimitiveSetList = ys.get(child, '"PrimitiveSetList"')
				if PrimitiveSetList:
					indexArray = process_primitive_set_list(ys, PrimitiveSetList, n)
					
				UserDataContainer = ys.get(child, '"UserDataContainer"')
				if UserDataContainer:
					for UserData in UserDataContainer:
						Values = ys.get(UserData, '"Values"')
						if Values:
							for a in Values[0].children:
								values = ys.values(a.data, ':')
								Name = ys.getValue(values, '"Name"','""')
								Value = ys.getValue(values, '"Value"','""')
								if Name: atributes[Name] = Value
							
				VertexAttributeList = ys.get(child, '"VertexAttributeList"')
				if VertexAttributeList:
					vertexArray, texArray = getVertexAttributeList(ys, VertexAttributeList, n)
				
					
			if "UserDataContainer" in child.header:
				write(dbg, ['UserDataContainer'],n)
				Values = ys.get(child, '"Values"')
				if Values:
					for a in Values[0].children:
						values = ys.values(a.data, ':')
						for value in values:
							id = ys.getValue(values, value)
							write(dbg, [value, ':',id],n + 4)
			if "VertexAttributeList" in child.header:
				write(dbg, ['VertexAttributeList'],n)
				Bones = ys.get(child, '"Bones"')
				if Bones:
					write(dbg, ['Bones'],n + 4)
					values = ys.values(Bones[0].data, ':')
					ItemSize = ys.getValue(values, '"ItemSize"','i')
					write(dbg, ['"ItemSize"',':',ItemSize],n + 8)
					Uint16Array = ys.get(Bones[0],'"Uint16Array"')
					if Uint16Array:
						type = "Uint16Array"
						values = ys.values(Uint16Array[0].data, ':')
						File = ys.getValue(values, '"File"','""')
						Size = ys.getValue(values, '"Size"','i')
						Offset = ys.getValue(values, '"Offset"','i')
						Encoding = ys.getValue(values, '"Encoding"','""')
						write(dbg, ['"File"',':',File],n + 8)
						write(dbg, ['"Size"',':',Size],n + 8)
						write(dbg, ['"Offset"',':',Offset],n + 8)
						write(dbg, ['"Encoding"',':',Encoding],n + 8)
						
						if Encoding == 'varint':
							path = os.path.dirname(ys.filename)+os.sep + "model_file.bin.gz.txt"
							if os.path.exists(path)==False: path = os.path.dirname(ys.filename)+os.sep + "model_file.bin"
							if os.path.exists(path)==False: path = os.path.dirname(ys.filename)+os.sep + values['"File"'].split('"')[1]#+'.txt'
							if os.path.exists(path)==True:
								file = open(path, 'rb')
								g = BinaryReader(file)
								list = decode_varint(g, Offset, Size * ItemSize, type)
								#write(dbg, list, 0)
								for m in range(Size):
									bones.append(list[m * ItemSize: m * ItemSize + ItemSize])
								file.close()
						
						
				Weights = ys.get(child, '"Weights"')
				if Weights:
					write(dbg, ['Weights'],n + 4)
					values = ys.values(Weights[0].data, ':')
					ItemSize = ys.getValue(values, '"ItemSize"','i')
					write(dbg, ['"ItemSize"',':',ItemSize],n + 8)
					Float32Array = ys.get(Weights[0],'"Float32Array"')
					if Float32Array:
						values = ys.values(Float32Array[0].data, ':')
						File = ys.getValue(values, '"File"','""')
						Size = ys.getValue(values, '"Size"','i')
						Offset = ys.getValue(values, '"Offset"','i')
						Encoding = ys.getValue(values, '"Encoding"','""')
						write(dbg, ['"File"',':',File],n + 8)
						write(dbg, ['"Size"',':',Size],n + 8)
						write(dbg, ['"Offset"',':',Offset],n + 8)
						write(dbg, ['"Encoding"',':',Encoding],n + 8)
						
						if Encoding == 'varint':
							path = os.path.dirname(ys.filename)+os.sep + "model_file.bin.gz.txt"
							if os.path.exists(path)==False: path = os.path.dirname(ys.filename)+os.sep + "model_file.bin"
							if os.path.exists(path)==False: path = os.path.dirname(ys.filename)+os.sep + values['"File"'].split('"')[1]#+'.txt'
							if os.path.exists(path)==True:
								file = open(path, 'rb')
								g = BinaryReader(file)
								list = decode_varint(g, Offset, Size * ItemSize, type)
								#write(dbg, list, 0)
								file.close()
						else:
							path = os.path.dirname(ys.filename)+os.sep + "model_file.bin.gz.txt"
							if os.path.exists(path)==False: path = os.path.dirname(ys.filename)+os.sep + "model_file.bin"
							if os.path.exists(path)==False: path = os.path.dirname(ys.filename)+os.sep + values['"File"'].split('"')[1]#+'.txt'
							if os.path.exists(path)==True:
								file = open(path, 'rb')
								g = BinaryReader(file)
								g.seek(Offset)
								list = g.f(Size * ItemSize)
								#write(dbg, list, 0)
								for m in range(Size):
									weights.append(list[m * ItemSize: m * ItemSize + ItemSize])
								file.close()
								
				
				
		#logger.info("%s", (atributes		,))
		mesh = Mesh()	
		if len(bones)>0 and len(Weights)>0:
			mesh.BoneMap = BoneMap
			skin = Skin()
			mesh.skinList.append(skin)
			mesh.skinIndiceList = bones
			mesh.skinWeightList = weights
		if len(indexArray)>0:
			for [indices, mode] in indexArray:
				logger.info("%s", (mode, len(indices)	,))
				mat = Mat()
				mesh.matList.append(mat)
				mat.IDStart = len(mesh.indiceList)
				mat.IDCount = len(indices)
				mesh.indiceList.extend(indices)
				if mode == '"TRIANGLE_STRIP"':mat.TRISTRIP = True
				if mode == '"TRIANGLES"':mat.TRIANGLE = True
				
			indices = indexArray[0][0]
			mode = indexArray[0][1]	
			if len(vertexArray)==1:
				if vertexArray[0][1]=='"varint"':
					bytes = vertexArray[0][0]				
					ItemSize = vertexArray[0][2]
					if mode == '"TRIANGLE_STRIP"':
						bytes = decode_predict(indices, bytes, ItemSize)
					s1 = float(atributes['vtx_bbl_x'])
					s2 = float(atributes['vtx_bbl_y'])
					s3 = float(atributes['vtx_bbl_z'])
					s = [s1, s2, s3]			
					a1 = float(atributes['vtx_h_x'])
					a2 = float(atributes['vtx_h_y'])
					a3 = float(atributes['vtx_h_z'])
					a = [a1, a2, a3]
					floats = decodeQuantize(bytes, s,a, ItemSize)
					mesh.vertPosList = [floats[m: m + ItemSize]for m in range(0, len(floats),3)]
				else:
					list = vertexArray[0][0]
					mesh.vertPosList = list
					
			if len(texArray)==1:
				if texArray[0][1]=='"varint"':
					bytes = texArray[0][0]				
					ItemSize = texArray[0][2]
					if mode == '"TRIANGLE_STRIP"':
						bytes = decode_predict(indices, bytes, ItemSize)
					s1 = float(atributes['uv_0_bbl_x'])
					s2 = float(atributes['uv_0_bbl_y'])
					s = [s1, s2]			
					a1 = float(atributes['uv_0_h_x'])
					a2 = float(atributes['uv_0_h_y'])
					a = [a1, a2]
					floats = decodeQuantize(bytes, s,a, ItemSize)
					#mesh.vertUVList = [floats[m: m + ItemSize]for m in range(0, len(floats),ItemSize)]
					for m in range(0, len(floats),ItemSize):
						u, v = floats[m: m + ItemSize]
						mesh.vertUVList.append([u, 1 - v])
				else:
					list = texArray[0][0]
					mesh.vertUVList = list
		return mesh	

	def process_osg_material(self, node, n):
		logger.info('process_osg_material %s UID %s', node.get('Name'), node.get('UniqueID'))
		uid = node['UniqueID']
		mat = Mat()
		mat.name = node.get('Name')
		mat.rgbCol = node.get('Diffuse')
		mat.specCol = node.get('Specular')
		self.materials[uid] = mat
		return uid
		
	def process_osg_state_set(self, node, n):
		uid = node.get('UniqueID')
		logger.info('process_osg_state_set %s UID:%s', node.get('Name'), uid)

		if uid:
			matl = None
			attrs = node.get('AttributeList', [])
			for attr in attrs:
				matl = attr.get('osg.Material')
				if matl:
					mtl_uid = self.process_osg_material(matl, n+4)
					self.state_uid_to_mtl_uid[uid] = mtl_uid
					return mtl_uid
			if attrs and not matl:
				logger.warning('StateSet with AttributeList but without osg.Material')
			if not attrs:
				# link to existing state
				return self.state_uid_to_mtl_uid[uid]
		else:
			return None

	def get_matl_uid_from_state(self, state_node):
		attrs = state_node.get('AttributeList', [])
		for attr in attrs:
			mtl = attr.get('osg.Material')
			if mtl:
				return mtl.get('UniqueID')
		return None
			
			
	def process_geometry(self, node, n):
		logger.info('process_geometry %s(UID:%s)', node.get('Name'), node.get('UniqueID'))
		write(dbg, ['Geometry'], n)

		n += 4
		mode = None
		indices = []
		vertices = []
		textures = []
		attrs = {}
		
		primitive_set_list = node.get('PrimitiveSetList')
		if primitive_set_list:
			indices = self.process_primitive_set_list(primitive_set_list, n)
			
		user_data = node.get('UserDataContainer')
		if user_data:
			values = user_data.get('Values', [])
			for vert_h in values:
				name = vert_h.get('Name', '')
				value = vert_h.get('Value','')
				#if Name: write(dbg, [Name, Value],n + 4)
				if name: 
					attrs[name] = value
					
		vertex_attr_list_node = node.get('VertexAttributeList')
		if vertex_attr_list_node:
			vertices, textures = self.process_vertex_attrs(vertex_attr_list_node, n)

		mtl_uid = None
		# state_set = node.get('StateSet')		
		# if state_set:
		# 	osg_state_set = state_set.get('osg.StateSet')
		# 	if osg_state_set:
		# 		mtl_uid = self.process_osg_state_set(osg_state_set, n)

		logger.info('process_geometry has %d indices, %d vertices, %d tex, matl uid %s', 
			len(indices), len(vertices), len(textures), mtl_uid)
		mesh = Mesh()
		mesh.name = node.get('Name')
		if len(indices)>0:
			for indices_elem, mode in indices:
				logger.info('  len = %d (mode %s)', len(indices_elem), mode)
				mat = None
				if mtl_uid:
					mat = self.materials.get(mtl_uid)
				if not mat:
					mat = Mat()
				mesh.matList.append(mat)
				mesh.indiceList.extend(indices_elem)
				if mode == 'TRIANGLE_STRIP': mat.TRISTRIP = True
				if mode == 'TRIANGLES': mat.TRIANGLE = True
			
			indices_elem = indices[0][0]
			mode = indices[0][1]
			if len(vertices)==1:
				if vertices[0][1]=='varint':
					bytes = vertices[0][0]				
					item_size = vertices[0][2]
					if mode == 'TRIANGLE_STRIP':
						bytes = self.decode_predict(indices_elem, bytes, item_size)
					s1 = float(attrs['vtx_bbl_x'])
					s2 = float(attrs['vtx_bbl_y'])
					s3 = float(attrs['vtx_bbl_z'])
					vert_bbl = [s1, s2, s3]			
					a1 = float(attrs['vtx_h_x'])
					a2 = float(attrs['vtx_h_y'])
					a3 = float(attrs['vtx_h_z'])
					vert_h = [a1, a2, a3]
					floats = self.decode_quantize(bytes, vert_bbl, vert_h, item_size)
					mesh.vertPosList = [floats[m: m + item_size] for m in range(0, len(floats), 3)]
				else:
					list = vertices[0][0]
					mesh.vertPosList = list
					
			if len(textures)==1:
				if textures[0][1]=='varint':
					bytes = textures[0][0]				
					item_size = textures[0][2]
					if mode == 'TRIANGLE_STRIP':
						bytes = self.decode_predict(indices_elem, bytes, item_size)
					s1 = float(attrs['uv_0_bbl_x'])
					s2 = float(attrs['uv_0_bbl_y'])
					vert_bbl = [s1, s2]			
					a1 = float(attrs['uv_0_h_x'])
					a2 = float(attrs['uv_0_h_y'])
					vert_h = [a1, a2]
					floats = self.decode_quantize(bytes, vert_bbl, vert_h, item_size)
					for m in range(0, len(floats), item_size):
						u, values = floats[m: m + item_size]
						mesh.vertUVList.append([u, 1 - values])

				else:
					list = textures[0][0]
					mesh.vertUVList = list				
			
		return mesh	

		
	def process_osg_matrixtransform(self, node, n, parent_bone):
		name = node.get('Name')
		write(dbg, ['MatrixTransform', name], n)
		n += 4

		bone = Bone()	
		bone.name = self.gen_bone_name(node)
		self.skeleton.boneList.append(bone)
		bone.parentName = parent_bone.name
		
		if name:
			name = self.getSplitName(name, '_', -1)
			write(dbg, [name],n)
			#if len(Name)<25: bone.name = Name
			self.obj2bone[name] = bone.name

		if 'Matrix' in node:
			floats = node['Matrix']
			write(dbg, floats, n)
			bone.matrix = Matrix4x4(floats)
			bone.matrix *= parent_bone.matrix
		
		for child in node.get('Children', []):
			self.process_child(child, n, bone)
			
	def gen_bone_name(self, node):
		return '{0}(UID:{1})/{2}'.format(
			node.get('Name', ''), 
			node.get('UniqueID', ''),
			str(len(self.skeleton.boneList)),
		)

	def process_osg_skeleton(self, node, n, parent_bone):
		name = node.get('Name')
		write(dbg, ['Skeleton', name], n)
		n += 4

		bone = Bone()	
		bone.name = self.gen_bone_name(node)
		self.skeleton.boneList.append(bone)
		bone.parentName = parent_bone.name
		
		self.firstmatrix = parent_bone.matrix
		
		
		if name:
			name = self.getSplitName(name, '_',-1)
			#logger.info("%s", (Name,))
			write(dbg, [name], n)
			#if len(Name)<25: bone.name = Name
			self.obj2bone[name] = bone.name
		
		if 'Matrix' in node:
			floats = node['Matrix']
			write(dbg, floats, n)
			bone.matrix = Matrix4x4(floats)
			bone.matrix *= parent_bone.matrix
		for child in node.get('Children', []):
			self.process_child(child, n, bone)
		

	def process_osg_rig_geometry(self, node, n, parent_bone):	
		write(dbg, ['RigGeometry'],n)			
		mesh = self.getRigGeometry(node, n)
		if len(mesh.vertPosList)>0:
			self.model.meshList.append(mesh)
			mesh.matrix = parent_bone.matrix
							
		n += 4
		for child in node.get('Children', []):
			self.process_child(child, n, parent_bone)
	

	def process_osg_geometry(self, node, n, parent_bone):
		write(dbg, ['Geometry'], n)
		mesh = self.process_geometry(node, n)
		if len(mesh.vertPosList)>0:
			self.model.meshList.append(mesh)
			mesh.matrix = parent_bone.matrix

		for child in node.get('Children', []):
			self.process_child(child, n+4, parent_bone)
		

	def process_osg_bone(self, node, n, parent_bone):
		write(dbg, ['Bone'], n)
		bone = Bone()		
		bone.name = self.gen_bone_name(node)
		bone.parentName = parent_bone.name
		self.skeleton.boneList.append(bone)

		n += 4
		name = node.get('Name')
		if name:
			name = self.getSplitName(name, '_', -1)
			write(dbg, [name],n)
			#logger.info("%s", (Name,))
			#if len(Name)<25: bone.name = Name
			self.obj2bone[name] = bone.name
				
		matrix = node.get('Matrix')
		if matrix:		
			bone.matrix = Matrix4x4(matrix)
			bone.matrix *= parent_bone.matrix
				
		inv_matrix = node.get('InvBindMatrixInSkeletonSpace')
		if inv_matrix:
			bindbone = Bone()
			#if Name: bindbone.name = Name
			bindbone.name = bone.name
			self.bindskeleton.boneList.append(bindbone)
			write(dbg, [inv_matrix], n + 4)
			matrix = Matrix4x4(inv_matrix).invert()
			bindbone.matrix = matrix * self.firstmatrix
				
		for child in node.get('Children', []):
			self.process_child(child, n, bone)
			

	def process_child(self, node, n, parent_bone):
		child_type, child_obj = next(iter(node.items()))
		write(dbg, ['Child', child_type], n)
		logger.info('process_child %s', child_type)
		n += 4	
		if child_type == 'osg.MatrixTransform':
			self.process_osg_matrixtransform(child_obj, n, parent_bone)
		elif child_type == 'osg.Node':
			self.process_osg_node(child_obj, n, parent_bone)
		elif child_type == 'osgAnimation.Skeleton':
			self.process_osg_skeleton(child_obj, n, parent_bone)
		elif child_type == 'osgAnimation.RigGeometry':
			self.process_osg_rig_geometry(child_obj, n, parent_bone)
		elif child_type == 'osg.Geometry':
			self.process_osg_geometry(child_obj, n, parent_bone)
		elif child_type == 'osgAnimation.Bone':
			self.process_osg_bone(child_obj, n, parent_bone)
		
		
	def process_osg_node(self, node, n, boneParent):
		name = node.get('Name')
		logger.info('process_osgnode %s', name)
		write(dbg, ['Node', name], n)
		n += 4
		
		bone = Bone()	
		bone.name = self.gen_bone_name(node)
		self.skeleton.boneList.append(bone)
		bone.parentName = boneParent.name
		bone.matrix = boneParent.matrix
		
		if name:
			#Name = getSplitName(Name, '_',-1)
			write(dbg, [name], n)
			#if len(Name)<25: bone.name = Name
			self.obj2bone[name] = bone.name
		
		for child in node.get('Children', []):
			self.process_child(child, n, bone)
	
					
	def bindPose(self, bindSkeleton, poseSkeleton, meshObject):
		#logger.info("%s", ('BINDPOSE',))
		mesh = meshObject.getData(mesh = 1)		
		poseBones = poseSkeleton.getData().bones
		bindBones = bindSkeleton.getData().bones	
		#mesh.transform(meshObject.matrixWorld)	
		mesh.update()
		for vert in mesh.verts:
			index = vert.index
			skinList = mesh.getVertexInfluences(index)
			vco = vert.co.copy()*meshObject.matrixWorld
			vector = Vector()
			sum = 0
			for skin in skinList:
				bone = skin[0]							
				weight = skin[1]	
				if bone in bindBones.keys() and bone in poseBones.keys():	
					matA = bindBones[bone].matrix['ARMATURESPACE']*bindSkeleton.matrixWorld
					matB = poseBones[bone].matrix['ARMATURESPACE']*poseSkeleton.matrixWorld
					vector += vco * matA.invert()*matB * weight
					sum += weight
				else:
					vector = vco
					break
			vert.co = vector
		mesh.update()
		Blender.Window.RedrawAll()	
	
		
	def parse_osgjs(self):

		with open(self.filename, 'r') as f:
			root = json.load(f)
			logger.info('loaded %s, v%s', root['Generator'], root['Version'])
		
		n = 0
		root_bone = Bone()
		root_bone.matrix = Matrix().resize4x4()
		root_bone.name = str(len(self.skeleton.boneList))
		root_bone.name = 'scene'
		self.skeleton.boneList.append(root_bone)

		self.process_osg_node(root['osg.Node'], n, root_bone)

		logger.info('#'*40)
		logger.info('Meshes: %d; bones:%d', len(self.model.meshList), len(self.skeleton.boneList) )

		if len(self.bindskeleton.boneList)>0: 
			self.bindskeleton.draw()	
		
		for mesh in self.model.meshList:
			if len(mesh.skinList)>0:
				for map in mesh.BoneMap:
					if map == 0: break
					mesh.boneNameList.append(self.obj2bone[map])
		
		for mesh in self.model.meshList:
			if len(mesh.skinList)>0:
				self.skeleton.NICE = True
				self.skeleton.draw()			
				break

		for mesh in self.model.meshList:
			mesh.draw()
			if mesh.object:
				if len(mesh.skinList)>0:
					if BINDPOSE == 1:
						if self.bindskeleton.object and self.skeleton.object:
							mesh.object.getData(mesh = 1).transform(mesh.matrix)
							mesh.object.getData(mesh = 1).update()
							##mesh.object.setMatrix(mesh.matrix)
							bindPose(self.bindskeleton.object, self.skeleton.object, mesh.object)
							##mesh.object.setMatrix(mesh.matrix.invert()*mesh.object.matrixWorld)
							scene = bpy.data.scenes.active
							scene.objects.unlink(self.bindskeleton.object)
					else:
						if self.bindskeleton.object and self.skeleton.object:
							mesh.object.getData(mesh = 1).transform(mesh.matrix)
							mesh.object.getData(mesh = 1).update()
				else:		
					mesh.object.setMatrix(mesh.matrix)
			
		n = 0	
		animations = root.get('osgAnimation.Animation')		
		if animations:
			for animation in animations:	
				self.getAnimation(animation, n)
		
 
def open_file_handler(filename):
	global dbg
	dbg = open('dbg.txt','w')
	try:
		logger.info('open_file_handler: %s', filename)
		importer = Importer(filename)
	except Exception as e:
		logger.exception('Parsing failed')
	finally:	
		dbg.close()
	

	
def etap1(input, ItemSize):
	n = len(input)/ItemSize
	r = 0
	output = [0]*len(input)
	while(r<n):
		a = r * ItemSize
		s = 0
		while(s<ItemSize):
			output[a + s] = input[r + n * s]
			s += 1	
		r += 1
	return output	
	
def etap2(input, ItemSize, atributes):
	i = [atributes['"bx"'],atributes['"by"'],atributes['"bz"']]
	n = [atributes['"hx"'],atributes['"hy"'],atributes['"hz"']]
	#start = [atributes['"ox"'],atributes['"oy"'],atributes['"oz"']]
	

	a = len(input)/ItemSize
	s = 0
	output = [0]*len(input)
	while(s<a):
		o = s * ItemSize
		u = 0
		while(u<ItemSize):
			output[o + u] = i[u]+input[o + u]*n[u];
			u += 1	
		s += 1
		
	#start.extend(output)
	#start[0] = atributes['"ot"']	
	return output	
	
def etap3(input, ItemSize):
	i = ItemSize|1
	n = 1
	r = len(input)/i
	while(n<r):
		a = (n - 1)*i
		s = n * i
		o = 0
		while(o<i):			
			input[s + o]+=input[a + o]
			o += 1	
		n += 1
	return input
	
def etap4(input):
	e = 1
	i = len(input)/4
	while(e<i):
		n = 4 * (e-1)
		r = 4 * e
		a = input[n]
		s = input[n + 1]
		o = input[n + 2]
		u = input[n + 3]
		l = input[r]
		h = input[r + 1]
		c = input[r + 2]
		d = input[r + 3]
		input[r] = a * d + s * c - o * h + u * l
		input[r + 1]=-a * c + s * d + o * l + u * h
		input[r + 2] = a * h - s * l + o * d + u * c
		input[r + 3]=-a * l - s * h - o * c + u * d
		e += 1
	return	input
	
def int3float4(input, atributes, ItemSize):
	c = 4
	d = atributes['"epsilon"']
	p = int(atributes['"nphi"'])
	e = [0]*len(input)*4
	i = 1.57079632679
	n = 6.28318530718
	r = 3.14159265359
	a = .01745329251
	s = .25
	o = 720
	u = 832
	l = 47938362584151635e-21
	h = {}
	f = True
	
	d = d or s
	p = p or o
	g = math.cos(d * a)
	m = 0
	v = 0
	_ = []
	
	v = (p + 1)*(u + 1)*3
	_ = [None]*v
	
	b = r/float(p - 1)
	x = i/float(p - 1)
	
	if f: y = 3
	else: y = 2
		
		
	m = 0
	v = len(input)/y
	while(m<v):
		A = m * c
		S = m * y
		C = input[S]
		w = input[S + 1]
		if c == 0:
			if f == 0:
				if (C&-1025)!=4:		
					e[A + 3]=-1
				else:
					e[A + 3] = 1
		M = None
		T = None
		E = None
		I = 3 * (C + p * w)		
		M = _[I]
		if	M == None:				
			N = C * b
			k = cos(N)
			F = sin(N)
			N += x
			D = (g - k * cos(N))/float(max(1e-5, F * sin(N)))
			if D>1: D = 1
			else:
				if D<-1: D = -1
			P = w * n/float(math.ceil(r/float(max(1e-5, math.acos(D)))))
			M = _[I] = F * math.cos(P)
			T = _[I + 1] = F * math.sin(P)
			E = _[I + 2] = k
		else: 
			T = _[I + 1]
			E = _[I + 2]
		if f:
			R = input[S + 2]*l
			O = math.sin(R)
			e[A] = O * M
			e[A + 1] = O * T
			e[A + 2] = O * E
			e[A + 3] = math.cos(R)
			#write(dbg, [A, e[A],e[A + 1],e[A + 2],e[A + 3]],0)
		else: 
			e[A] = M
			e[A + 1] = T
			e[A + 2] = E
		m += 1
	
	#write(dbg, _,0)
	return e	
	
Blender.Window.FileSelector(open_file_handler, 'Import', 'file.osgjs') 
