
# Group number 12

# 2017B5A70822H	Chatrik Singh S Mangat
# 2017B5A71149H	Ashi Sinha
# 2018AAPS0418H	Aakash Bansal
# 2018AAPS0493H	Dev Kirti Phartiyal





import numpy as np
import random
import os
import time  
import hashlib  
import pickle

# Checks if array contains only 0s and 1s
def bin_check(arr):
	flag = 0
	for i in arr:
		if(arr[i] != 0 and arr[i] != 1):
			flag = 1
			break
	if(flag == 0):
		return 0
	else:
		return 1

# Takes Key from user and generates all sub_keys required for DES
# Permute Key using PC-1 (64 bits -> 56 bits)
# Generate rotations using Shifts
# Permute all subkeys using PC-2 (56 bits -> 48 bits)
def get_perm_keys(inp_key):				
	pc_1_mat = {1: 57, 2: 49, 3: 41, 4: 33, 5: 25, 6: 17, 7: 9, 8: 1, 9: 58, 10: 50, 11: 42, 12: 34, 13: 26, 14: 18, 15: 10, 16: 2, 17: 59, 18: 51, 19: 43, 20: 35, 21: 27, 22: 1, 23: 11, 24: 3, 25: 60, 26: 52, 27: 44, 28: 36, 29: 63, 30: 55, 31: 47, 32: 39, 33: 31, 34: 23, 35: 15, 36: 7, 37: 62, 38: 54, 39: 46, 40: 38, 41: 30, 42: 22, 43: 14, 44: 6, 45: 61, 46: 53, 47: 45, 48: 37, 49: 29, 50: 21, 51: 13, 52: 5, 53: 28, 54: 20, 55: 12, 56: 4}
	
	perm_key = {}
	for i in pc_1_mat:
		perm_key[i] = inp_key[pc_1_mat[i]]	
	
	c0 = {}
	d0 = {}
	
	for i in perm_key:
		if(i <= 28):
			c0[i] = perm_key[i]
			continue
		if(i >= 29):
			d0[i-28] = perm_key[i]	
			continue	
	rot_c = {0: c0}
	rot_d = {0: d0}
	
	shifts = {1: 1, 2: 1, 3: 2, 4: 2, 5: 2, 6: 2, 7: 2, 8: 2, 9: 1, 10: 2, 11: 2, 12: 2, 13: 2, 14: 2, 15: 2, 16: 1}
	
	for i in range(1,17):
		rot_c[i] = {}
		rot_d[i] = {}
		for j in range(1,len(rot_c[i-1])+1):
			if(j+shifts[i] <= 28):
				rot_c[i][j] = rot_c[i-1][j+shifts[i]]
				rot_d[i][j] = rot_d[i-1][j+shifts[i]]
			else:
				rot_c[i][j] = rot_c[i-1][j+shifts[i]-28]
				rot_d[i][j] = rot_d[i-1][j+shifts[i]-28]
	
	temp_keys = {}
	for i in rot_c:
		one_temp_key = {}
		for j in range(1,57):
			if(j <= 28):
				one_temp_key[j] = rot_c[i][j]
			else:
				one_temp_key[j] = rot_d[i][j-28]
		temp_keys[i] = one_temp_key		
	
	pc_2_mat = {1: 14, 2: 17, 3: 11, 4: 24, 5: 1, 6: 5, 7: 3, 8: 28, 9: 15, 10: 6, 11: 21, 12: 10, 13: 23, 14: 19, 15: 12, 16: 4, 17: 26, 18: 8, 19: 16, 20: 7, 21: 27, 22: 20, 23: 13, 24: 2, 25: 41, 26: 52, 27: 31, 28: 37, 29: 47, 30: 55, 31: 30, 32: 40, 33: 51, 34: 45, 35: 33, 36: 48, 37: 44, 38: 49, 39: 39, 40: 56, 41: 34, 42: 53, 43: 46, 44: 42, 45: 50, 46: 36, 47: 29, 48: 32}
	
	fin_keys = {}
	
	for i in range(1,17):
		one_fin_key = {}
		for j in pc_2_mat:
			one_fin_key[j] = temp_keys[i][pc_2_mat[j]]
		fin_keys[i] = one_fin_key		
	
	return fin_keys			

# Implementation of the f() function
# Break input into 8 pieces of size 6 bits
# Find corresponding 4 bit representation for each piece using S
# Concatenate all pieces to get 32 bit value and permute using P
def f_sub(xor_temp):
	
	sub_mat = {
			# S1
		1: [[14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7],
			[0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8],
			[4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0],
			[15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13]],

			# S2
		2: [[15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10],
			[3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5],
			[0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15],
			[13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9]],

			# S3
		3: [[10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8],
			[13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1],
			[13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7],
			[1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12]],

			# S4
		4: [[7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15],
			[13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9],
			[10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4],
			[3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14]],

			# S5
		5: [[2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9],
			[14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6],
			[4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14],
			[11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3]],

			# S6
		6: [[12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11],
			[10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8],
			[9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6],
			[4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13]],

			# S7
		7: [[4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1],
			[13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6],
			[1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2],
			[6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12]],

			# S8
		8: [[13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7],
			[1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2],
			[7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8],
			[2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11]]
	}
	
	val_list_b = {}
	for i in range(0,8):
		b_temp = []
		k = 1
		for j in xor_temp:
			b_temp.append(xor_temp[j+6*i])
			k = k+1
			if(k > 6):
				break
		val_list_b[i+1] = b_temp		
	
	val_list_s = {}
	for i in val_list_b:
		row = 2*val_list_b[i][0]+val_list_b[i][5]
		col = int("".join(str(k) for k in val_list_b[i][1:5]),2)
		s_int = sub_mat[i][row][col]	
		s_temp = [int(k) for k in bin(s_int)[2:].zfill(4)]
		val_list_s[i] = s_temp
	
	val_s = {}
	k = 1
	for i in val_list_s:
		for j in val_list_s[i]:
			val_s[k] = j
			k = k+1
	
	p_mat = {1: 16, 2: 7, 3: 20, 4: 21, 5: 29, 6: 12, 7: 28, 8: 17, 9: 1, 10: 15, 11: 23, 12: 26, 13: 5, 14: 18, 15: 31, 16: 10, 17: 2, 18: 8, 19: 24, 20: 14, 21: 32, 22: 27, 23: 3, 24: 9, 25: 19, 26: 13, 27: 30, 28: 6, 29: 22, 30: 11, 31: 4, 32: 25}	
	
	fin_val_f = {}
	for i in p_mat:
		fin_val_f[i] = val_s[p_mat[i]]	
	
	return fin_val_f		
			
# Handles 16 rounds of DES
# Permute input Plain Text using IP and divide into L0 and R0
# Right half of (n)th round becomes Left half of (n+1)th round
# Expand Right half using E and XOR with corresponding subkey
# Call f() on XOR'ed value, result is Right half of (n+1)th round
# Concatenate R16 + L16 and permute using IP_inv, return Cipher   
def encode(inp_pt,fin_keys):
	
	ip_mat = {1: 58, 2: 50, 3: 42, 4: 34, 5: 26, 6: 18, 7: 10, 8: 2, 9: 60, 10: 52, 11: 44, 12: 36, 13: 28, 14: 20, 15: 12, 16: 4, 17: 62, 18: 54, 19: 46, 20: 38, 21: 30, 22: 22, 23: 14, 24: 6, 25: 64, 26: 56, 27: 48, 28: 40, 29: 32, 30: 24, 31: 16, 32: 8, 33: 57, 34: 49, 35: 41, 36: 33, 37: 25, 38: 17, 39: 9, 40: 1, 41: 59, 42: 51, 43: 43, 44: 35, 45: 27, 46: 19, 47: 11, 48: 3, 49: 61, 50: 53, 51: 45, 52: 37, 53: 29, 54: 21, 55: 13, 56: 5, 57: 63, 58: 55, 59: 47, 60: 39, 61: 31, 62: 23, 63: 15, 64: 7}

	perm_pt = {}
	for i in ip_mat:
		perm_pt[i] = inp_pt[ip_mat[i]]
	
	l0 = {}
	r0 = {}
	
	for i in perm_pt:
		if(i <= 32):
			l0[i] = perm_pt[i]
			continue
		if(i >= 33):
			r0[i-32] = perm_pt[i]	
			continue
			
	val_l = {0: l0}
	val_r = {0: r0}
	
	e_mat = {1: 32, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 7: 4, 8: 5, 9: 6, 10: 7, 11: 8, 12: 9, 13: 8, 14: 9, 15: 10, 16: 11, 17: 12, 18: 13, 19: 12, 20: 13, 21: 14, 22: 15, 23: 16, 24: 17, 25: 16, 26: 17, 27: 18, 28: 19, 29: 20, 30: 21, 31: 20, 32: 21, 33: 22, 34: 23, 35: 24, 36: 25, 37: 24, 38: 25, 39: 26, 40: 27, 41: 28, 42: 29, 43: 28, 44: 29, 45: 30, 46: 31, 47: 32, 48: 1}
	
	exp_r = {}
	
	for i in range(1,17):
		val_l[i] = val_r[i-1].copy()
		val_r[i] = {}	
		
		exp_r[i-1] = {}
		for j in e_mat:
			exp_r[i-1][j] = val_r[i-1][e_mat[j]]
		
		xor_temp = {}
		for j in exp_r[i-1]:
			xor_temp[j] = exp_r[i-1][j]^fin_keys[i][j]
		
		fin_val_f = f_sub(xor_temp)
		
		for j in fin_val_f:
			val_r[i][j] = val_l[i-1][j] ^ fin_val_f[j]
	
	temp_ct = {}
	for i in range(1,65):
		if(i <= 32):
			temp_ct[i] = val_r[16][i]
		else:
			temp_ct[i] = val_l[16][i-32]	
	
	ip_inv_mat = {1: 40, 2: 8, 3: 48, 4: 16, 5: 56, 6: 24, 7: 64, 8: 32, 9: 39, 10: 7, 11: 47, 12: 15, 13: 55, 14: 23, 15: 63, 16: 31, 17: 38, 18: 6, 19: 46, 20: 14, 21: 54, 22: 22, 23: 62, 24: 30, 25: 37, 26: 5, 27: 45, 28: 13, 29: 53, 30: 21, 31: 61, 32: 29, 33: 36, 34: 4, 35: 44, 36: 12, 37: 52, 38: 20, 39: 60, 40: 28, 41: 35, 42: 3, 43: 43, 44: 11, 45: 51, 46: 19, 47: 59, 48: 27, 49: 34, 50: 2, 51: 42, 52: 10, 53: 50, 54: 18, 55: 58, 56: 26, 57: 33, 58: 1, 59: 41, 60: 9, 61: 49, 62: 17, 63: 57, 64: 25}
	
	fin_ct = {}	
	for i in ip_inv_mat:
		fin_ct[i] = temp_ct[ip_inv_mat[i]]
			
	return fin_ct	

# Encrypts Plaintext (64 bit) using User Key (64 bit)
# Input is in the form of Strings of 0s and 1s	
# Returns Cipher Text (64 bit) in same format as input
def encrypt(pt,key):	
	inp_key = {}
	inp_pt = {}
	for i in range(len(key)):
		inp_key[i+1] = int(key[i])
		inp_pt[i+1] = int(pt[i])
	#print("\n**Encryption**\n")
		
	#if(not bin_check(inp_pt)):
		#print("Plain Text Size:",len(inp_pt))
		#print("Plain Text:",pt)
	#else:
		#print("Invalid Plain Text", inp_pt)
		#return		

	#if(not bin_check(inp_key)):
		#print("Key Size:",len(inp_key))
		#print("Key:",key)
	#else:
		#print("Invalid Key", inp_key)
		#return			

	fin_keys = get_perm_keys(inp_key)
	#print("\n**Keys Generated**\n")
	#print("Final Key Size:",len(fin_keys[1]))
	#print("Number of Final Keys:",len(fin_keys))	
	
	fin_ct = encode(inp_pt,fin_keys)
	#print("\n**Cipher Text Generated**\n")
	#print("Cipher Text Size:",len(fin_ct))
	
	ct = ""
	for i in fin_ct:
		ct = ct + str(fin_ct[i])
	
	#print("Cipher Text:",ct)
	
	return ct

# Decrypts Ciphertext (64 bit) using User Key (64 bit)
# Input is in the form of Strings of 0s and 1s	
# Returns Plain Text (64 bit) in same format as input
def decrypt(ct,key):	
	inp_key = {}
	inp_ct = {}
	for i in range(len(key)):
		inp_key[i+1] = int(key[i])
		inp_ct[i+1] = int(ct[i])
	print("**Decryption**")
		
	if(not bin_check(inp_ct)):
		print("Cipher Text Size:",len(inp_ct))
		print("Cipher Text:",ct)
	else:
		print("Invalid Cipher Text", inp_ct)
		return		

	if(not bin_check(inp_key)):
		print("Key Size:",len(inp_key))
		print("Key:",key)
	else:
		print("Invalid Key", inp_key)
		return			

	fin_keys = get_perm_keys(inp_key)
	
	# Only thing different between Encryption and Decryption is reversal of subkeys 
	reverse_keys = {}
	for i in fin_keys:
		reverse_keys[17-i] = fin_keys[i].copy() 
	
	print("\n**Keys Generated**\n")
	print("Final Key Size:",len(reverse_keys[1]))
	print("Number of Final Keys:",len(reverse_keys))	
	
	fin_pt = encode(inp_ct,reverse_keys)
	print("\n**Plain Text Generated**\n")
	print("Plain Text Size:",len(fin_pt))
	
	pt = ""
	for i in fin_pt:
		pt = pt + str(fin_pt[i])
	
	print("Plain Text:",pt)
	
	return pt	

# Implementation of a block:
class Block(object):  
      
    def __init__(self, index, proof, previous_hash, transactions):  
        self.index = index  
        self.proof = proof  
        self.previous_hash = previous_hash  
        self.transactions = transactions  
        self.timestamp = time.time()  
  
    def __repr__(self):
        return "<Block index:%s proof:%s  transactions:%s timestamp:%s previous_hash:%s>" % (self.index,self.proof,self.transactions,self.timestamp,self.previous_hash)

    @property  
    def get_block_hash(self):  
        block_string = "{}{}{}{}{}".format(self.index, self.proof, self.previous_hash, self.transactions, self.timestamp)
        block_string_hex = hashlib.sha256(block_string.encode()).hexdigest()
        res = str("{0:0256b}".format(int(block_string_hex, 16)))
        key = str("{0:064b}".format(int("133457799BBCDFF1", 16)))
        des_encrypt = encrypt(res[0:64],key) + encrypt(res[64:128],key) + encrypt(res[128:192],key) + encrypt(res[192:256],key)

        return des_encrypt

# Implementation of Blockchain:
class BlockChain(object):  
      
    def __init__(self):  
        self.chain = []  
        self.current_node_transactions = []  
        self.create_genesis_block()  
      
    def create_genesis_block(self):  
        self.create_new_block(proof=0, previous_hash=0) 
  
    def create_new_block(self, proof, previous_hash):  
      block = Block(  
        index=len(self.chain),  
        proof=proof,  
        previous_hash=previous_hash,  
        transactions=self.current_node_transactions  
      )  
      self.current_node_transactions = []   
  
      self.chain.append(block)  
      return block 

    def loadData(self, dict1):
        l = len(dict1["Chain"])
        for i in range(1,l):
            self.chain.append(dict1["Chain"][i])

    def create_new_transaction(self, sender, recipient, amount):  
      self.current_node_transactions.append({  
        'sender': sender,  
        'recipient': recipient,  
        'amount': amount  
      })  
  
      return self.get_last_block.index + 1 
    
	
    @staticmethod
    def mineBlock(previous_proof):
        difficulty = 1
        prefix = '1' * difficulty
        for i in range(1000):
          proof = hashlib.sha256((str(previous_proof) + str(i)).encode()).hexdigest()
          if proof.startswith(prefix):
            return i 

    @property  
    def get_last_block(self):  
        return self.chain[-1]

def verifyTransaction(sender_p, sender_g, x):
  y = (sender_g**x) % sender_p
  r = round(random.random()* sender_p)

  h = (sender_g**r) % sender_p
  b = round(random.random())

  s = (r + b*x)%(sender_p-1)

  if ((sender_g**s) % sender_p == h*(y**b)%sender_p):
    return True
  else:
    return False

def viewUser(name):
  for user in users:
    if name in user.values():
      for i in user:
        print(i,user[i])

blockchain = BlockChain()  
# Specify path to directory containing crypto.py
# Final path example: PATH_TO_crypto.py \data.pkl
# data.pkl is the file which contains the transactions,if this file exists,we open the file else we create a new file

if os.path.exists(r"C:\Users\ashi sinha\Downloads\data.pkl"):
    a_file = open("data.pkl", "rb")
    dictionary_data = pickle.load(a_file)
    A = dictionary_data["A"]
    B = dictionary_data["B"]
    C = dictionary_data["C"]
    blockchain.loadData(dictionary_data)
    a_file.close()
    
else: #example users :
    A = {"Name": "Monty", "Balance": 100} 
    A["Transactions"] = []
    B = {"Name": "Bob", "Balance": 50}
    B["Transactions"] = [] 
    C = {"Name": "Alice", "Balance": 500} 
    C["Transactions"] = []

users = [A,B,C]

flag = 2
while flag != 0:
    flag = int(input('Transaction: 1\tView Users: 2\tView Blockchain: 3\t Exit: 0\n'))
    if flag==1:
      print("Transaction: ")
      last_block = blockchain.get_last_block  
      last_proof = last_block.proof  
      proof = blockchain.mineBlock(last_proof)

      sender = input("Enter Sender: ")  
      recipient = input(" Enter Recipient: ")  
      amount = int(input("Enter Amount: "))
      
      tr = "Sender: "+sender+", Recipient: "+recipient+", Amount: "+str(amount)

      for user in users:
        if sender in user.values():
          if user["Balance"] >= amount:
            if verifyTransaction(11, 2, amount):
              user["Balance"] -= amount
              blockchain.create_new_transaction(sender, recipient, amount)  
              last_hash = last_block.get_block_hash  
              block = blockchain.create_new_block(proof, last_hash)
              user["Transactions"].append(tr)

              for user2 in users:
                if recipient in user2.values():
                  user2["Balance"] += amount
                  user2["Transactions"].append(tr)
                  print(tr)
                  break  
          else:
            print("insufficient amount")
            break
      print("\n")

    # 2 view user
    elif flag==2:
      user = input("Enter Name to view Transaction details: ")
      viewUser(user)
      print("\n")

    # 3 view blockchain
    elif flag==3:
      print(*blockchain.chain, sep = "\n")

dictionary_data = {"A": A, "B": B,"C": C, "Chain": blockchain.chain}

a_file = open("data.pkl", "wb")
pickle.dump(dictionary_data, a_file)
a_file.close()
