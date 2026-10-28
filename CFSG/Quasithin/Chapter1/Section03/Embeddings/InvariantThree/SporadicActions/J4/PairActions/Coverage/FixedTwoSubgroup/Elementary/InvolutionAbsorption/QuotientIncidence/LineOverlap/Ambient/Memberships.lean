module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Evaluations

/-!
# Constructive membership certificates in the actual ATLAS max4

Every row is obtained by multiplying or inverting already certified members
of max4. The search that supplied these words is not used as a premise.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates

open Janko4 Janko4.GeneratorCertificates Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] Janko4.modelGroup

theorem mem_max4U : InMax4 r25 := by
  refine ⟨max4U, ?_, eval_max4U⟩
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem mem_max4V : InMax4 r22 := by
  refine ⟨max4V, ?_, eval_max4V⟩
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))


theorem member_0 : InMax4 r26 :=
  InMax4.inv mem_max4V product_27

theorem member_1 : InMax4 r94 :=
  InMax4.mul member_0 mem_max4U product_96

theorem member_2 : InMax4 r95 :=
  InMax4.mul member_1 member_0 product_97

theorem member_3 : InMax4 r96 :=
  InMax4.mul member_2 mem_max4U product_98

theorem member_4 : InMax4 r97 :=
  InMax4.inv member_3 product_99

theorem member_5 : InMax4 r98 :=
  InMax4.mul member_4 mem_max4U product_100

theorem member_6 : InMax4 r99 :=
  InMax4.mul mem_max4U member_3 product_101

theorem member_7 : InMax4 r100 :=
  InMax4.mul member_4 mem_max4V product_102

theorem member_8 : InMax4 r101 :=
  InMax4.mul member_7 mem_max4U product_103

theorem member_9 : InMax4 r102 :=
  InMax4.mul member_8 member_0 product_104

theorem member_10 : InMax4 r103 :=
  InMax4.mul member_9 mem_max4U product_105

theorem member_11 : InMax4 r104 :=
  InMax4.mul member_10 mem_max4V product_106

theorem member_12 : InMax4 r105 :=
  InMax4.mul member_0 member_10 product_107

theorem member_one : InMax4 packedOne :=
  ⟨1, max4Subgroup.one_mem, by rw [map_one, decode_packedOne]⟩

theorem member_14 : InMax4 r29 :=
  InMax4.mul mem_max4U member_5 product_108

theorem member_15 : InMax4 r30 :=
  InMax4.mul member_14 member_0 product_32

theorem member_16 : InMax4 r106 :=
  InMax4.mul member_15 member_12 product_109

theorem member_17 : InMax4 r107 :=
  InMax4.mul member_16 mem_max4U product_110

theorem member_18 : InMax4 r108 :=
  InMax4.mul member_5 mem_max4V product_111

theorem member_19 : InMax4 r109 :=
  InMax4.mul member_11 member_18 product_112

theorem member_20 : InMax4 r110 :=
  InMax4.mul member_0 member_19 product_113

theorem member_21 : InMax4 r111 :=
  InMax4.mul mem_max4U member_20 product_114

theorem member_22 : InMax4 r112 :=
  InMax4.mul member_12 member_21 product_115

theorem member_23 : InMax4 r113 :=
  InMax4.mul member_22 member_17 product_116

theorem member_24 : InMax4 r114 :=
  InMax4.mul member_23 member_6 product_117

theorem member_25 : InMax4 r115 :=
  InMax4.mul member_24 member_6 product_118

theorem member_26 : InMax4 r116 :=
  InMax4.mul member_25 mem_max4U product_119

theorem member_27 : InMax4 r117 :=
  InMax4.mul member_26 member_11 product_120

theorem member_28 : InMax4 r118 :=
  InMax4.mul member_27 member_0 product_121

theorem member_29 : InMax4 r119 :=
  InMax4.mul member_28 member_0 product_122

theorem member_30 : InMax4 r120 :=
  InMax4.mul member_29 mem_max4U product_123

theorem member_31 : InMax4 r121 :=
  InMax4.inv member_30 product_124

theorem member_32 : InMax4 r122 :=
  InMax4.mul member_5 member_30 product_125

theorem member_33 : InMax4 r123 :=
  InMax4.mul member_32 member_6 product_126

theorem member_34 : InMax4 r124 :=
  InMax4.mul member_33 mem_max4U product_127

theorem member_35 : InMax4 r125 :=
  InMax4.mul member_34 member_0 product_128

theorem member_36 : InMax4 r126 :=
  InMax4.mul member_35 member_12 product_129

theorem member_37 : InMax4 r127 :=
  InMax4.mul member_36 member_31 product_130

theorem member_38 : InMax4 r128 :=
  InMax4.mul member_37 mem_max4U product_131

theorem member_39 : InMax4 r129 :=
  InMax4.mul member_38 member_11 product_132

theorem member_40 : InMax4 r130 :=
  InMax4.mul member_5 member_11 product_133

theorem member_41 : InMax4 r131 :=
  InMax4.mul member_40 member_11 product_134

theorem member_42 : InMax4 r132 :=
  InMax4.mul member_41 mem_max4V product_135

theorem member_43 : InMax4 r133 :=
  InMax4.mul member_42 member_11 product_136

theorem member_44 : InMax4 r134 :=
  InMax4.mul member_43 member_6 product_137

theorem member_45 : InMax4 r135 :=
  InMax4.mul member_44 member_39 product_138

theorem member_46 : InMax4 r136 :=
  InMax4.mul member_45 mem_max4U product_139

theorem member_47 : InMax4 r137 :=
  InMax4.mul member_46 member_0 product_140

theorem member_48 : InMax4 r138 :=
  InMax4.mul member_47 member_5 product_141

theorem member_49 : InMax4 r139 :=
  InMax4.mul member_48 member_12 product_142

theorem member_50 : InMax4 r140 :=
  InMax4.mul member_49 member_12 product_143

theorem member_51 : InMax4 r141 :=
  InMax4.mul member_50 member_0 product_144

theorem member_52 : InMax4 r142 :=
  InMax4.mul member_51 member_6 product_145

theorem member_53 : InMax4 r143 :=
  InMax4.inv member_52 product_146

theorem member_54 : InMax4 r28 :=
  InMax4.mul member_14 mem_max4U product_31

theorem member_55 : InMax4 r144 :=
  InMax4.mul member_54 member_11 product_147

theorem member_56 : InMax4 r145 :=
  InMax4.mul member_55 mem_max4V product_148

theorem member_57 : InMax4 r146 :=
  InMax4.mul member_56 member_11 product_149

theorem member_58 : InMax4 r147 :=
  InMax4.mul member_57 member_6 product_150

theorem member_59 : InMax4 r148 :=
  InMax4.mul member_58 member_39 product_151

theorem member_60 : InMax4 r149 :=
  InMax4.mul member_59 mem_max4U product_152

theorem member_61 : InMax4 r150 :=
  InMax4.mul member_60 member_5 product_153

theorem member_62 : InMax4 r151 :=
  InMax4.mul member_61 member_12 product_154

theorem member_63 : InMax4 r152 :=
  InMax4.mul member_62 member_12 product_155

theorem member_64 : InMax4 r153 :=
  InMax4.mul member_63 member_0 product_156

theorem member_65 : InMax4 r154 :=
  InMax4.mul member_64 member_5 product_157

theorem member_66 : InMax4 r155 :=
  InMax4.mul member_65 member_5 product_158

theorem member_67 : InMax4 r156 :=
  InMax4.inv member_66 product_159

theorem member_68 : InMax4 r157 :=
  InMax4.mul member_11 mem_max4V product_160

theorem member_69 : InMax4 r158 :=
  InMax4.mul member_68 member_5 product_161

theorem member_70 : InMax4 r159 :=
  InMax4.mul member_69 member_11 product_162

theorem member_71 : InMax4 r160 :=
  InMax4.mul member_70 mem_max4V product_163

theorem member_72 : InMax4 r161 :=
  InMax4.mul member_71 member_6 product_164

theorem member_73 : InMax4 r162 :=
  InMax4.mul member_72 mem_max4V product_165

theorem member_74 : InMax4 r163 :=
  InMax4.mul member_73 member_39 product_166

theorem member_75 : InMax4 r164 :=
  InMax4.mul member_74 mem_max4U product_167

theorem member_76 : InMax4 r165 :=
  InMax4.mul member_75 member_6 product_168

theorem member_77 : InMax4 r166 :=
  InMax4.mul member_76 member_11 product_169

theorem member_78 : InMax4 r167 :=
  InMax4.mul member_77 member_5 product_170

theorem member_79 : InMax4 r168 :=
  InMax4.mul member_78 member_12 product_171

theorem member_80 : InMax4 r169 :=
  InMax4.mul member_79 mem_max4U product_172

theorem member_81 : InMax4 r170 :=
  InMax4.mul member_80 member_6 product_173

theorem member_82 : InMax4 r171 :=
  InMax4.mul member_81 member_66 product_174

theorem member_83 : InMax4 r172 :=
  InMax4.mul member_82 member_52 product_175

theorem member_84 : InMax4 r173 :=
  InMax4.inv member_83 product_176

theorem member_85 : InMax4 r174 :=
  InMax4.mul member_31 member_84 product_177

theorem member_86 : InMax4 r175 :=
  InMax4.mul member_85 member_66 product_178

theorem member_87 : InMax4 r176 :=
  InMax4.mul member_53 member_31 product_179

theorem member_88 : InMax4 r177 :=
  InMax4.mul member_87 member_86 product_180

theorem member_89 : InMax4 r178 :=
  InMax4.mul member_88 member_67 product_181

theorem member_90 : InMax4 r179 :=
  InMax4.mul member_89 member_53 product_182

theorem member_91 : InMax4 r180 :=
  InMax4.mul member_90 member_31 product_183

theorem member_92 : InMax4 r181 :=
  InMax4.mul member_91 member_31 product_184

theorem member_93 : InMax4 r182 :=
  InMax4.inv member_92 product_185

theorem member_94 : InMax4 r183 :=
  InMax4.mul member_66 member_86 product_186

theorem member_95 : InMax4 r184 :=
  InMax4.mul member_94 member_31 product_187

theorem member_96 : InMax4 r185 :=
  InMax4.mul member_95 member_53 product_188

theorem member_97 : InMax4 r186 :=
  InMax4.mul member_96 member_53 product_189

theorem member_98 : InMax4 r187 :=
  InMax4.inv member_97 product_190

theorem member_99 : InMax4 r188 :=
  InMax4.mul member_93 member_5 product_191

theorem member_100 : InMax4 r189 :=
  InMax4.mul member_99 member_53 product_192

theorem member_101 : InMax4 r190 :=
  InMax4.mul member_100 member_84 product_193

theorem member_102 : InMax4 r191 :=
  InMax4.mul member_101 member_0 product_194

theorem member_103 : InMax4 r192 :=
  InMax4.mul member_102 member_67 product_195

theorem member_104 : InMax4 r193 :=
  InMax4.mul member_103 mem_max4V product_196

theorem member_105 : InMax4 r27 :=
  InMax4.mul mem_max4V mem_max4U product_28

theorem member_106 : InMax4 r194 :=
  InMax4.mul member_11 member_105 product_197

theorem member_107 : InMax4 r195 :=
  InMax4.mul member_5 member_106 product_198

theorem member_108 : InMax4 r196 :=
  InMax4.mul mem_max4U member_107 product_199

theorem member_109 : InMax4 r197 :=
  InMax4.mul member_6 member_108 product_200

theorem member_110 : InMax4 r198 :=
  InMax4.mul mem_max4V member_109 product_201

theorem member_111 : InMax4 r199 :=
  InMax4.mul member_30 member_110 product_202

theorem member_112 : InMax4 r200 :=
  InMax4.mul member_52 member_111 product_203

theorem member_113 : InMax4 r201 :=
  InMax4.mul member_30 member_112 product_204

theorem member_114 : InMax4 r202 :=
  InMax4.mul member_97 member_113 product_205

theorem member_115 : InMax4 r203 :=
  InMax4.mul member_83 member_114 product_206

theorem member_116 : InMax4 r204 :=
  InMax4.mul member_115 member_104 product_207

theorem member_117 : InMax4 r205 :=
  InMax4.mul member_116 mem_max4V product_208

theorem member_118 : InMax4 r206 :=
  InMax4.mul member_117 member_5 product_209

theorem member_119 : InMax4 r207 :=
  InMax4.mul member_118 member_5 product_210

theorem member_120 : InMax4 r208 :=
  InMax4.mul member_119 mem_max4U product_211

theorem member_121 : InMax4 r209 :=
  InMax4.mul member_120 member_6 product_212

theorem member_122 : InMax4 r210 :=
  InMax4.mul member_121 member_6 product_213

theorem member_123 : InMax4 r211 :=
  InMax4.mul member_122 member_0 product_214

theorem member_124 : InMax4 r212 :=
  InMax4.mul member_123 mem_max4U product_215

theorem member_125 : InMax4 r213 :=
  InMax4.mul member_124 member_67 product_216

theorem member_126 : InMax4 r214 :=
  InMax4.mul member_125 member_53 product_217

theorem member_127 : InMax4 r215 :=
  InMax4.mul member_126 member_31 product_218

theorem member_128 : InMax4 r216 :=
  InMax4.inv member_127 product_219

theorem member_129 : InMax4 r217 :=
  InMax4.mul member_11 member_5 product_220

theorem member_130 : InMax4 r218 :=
  InMax4.mul member_129 member_5 product_221

theorem member_131 : InMax4 r219 :=
  InMax4.mul member_130 mem_max4V product_222

theorem member_132 : InMax4 r220 :=
  InMax4.mul member_131 mem_max4U product_223

theorem member_133 : InMax4 r221 :=
  InMax4.mul member_132 member_52 product_224

theorem member_134 : InMax4 r222 :=
  InMax4.mul member_133 member_66 product_225

theorem member_135 : InMax4 r223 :=
  InMax4.mul member_134 member_31 product_226

theorem member_136 : InMax4 r224 :=
  InMax4.mul member_135 member_128 product_227

theorem member_137 : InMax4 r225 :=
  InMax4.inv member_136 product_228

theorem member_138 : InMax4 r226 :=
  InMax4.mul member_12 mem_max4V product_229

theorem member_139 : InMax4 r227 :=
  InMax4.mul member_138 member_11 product_230

theorem member_140 : InMax4 r228 :=
  InMax4.mul member_139 member_5 product_231

theorem member_141 : InMax4 r229 :=
  InMax4.mul member_140 member_11 product_232

theorem member_142 : InMax4 r230 :=
  InMax4.mul member_141 member_5 product_233

theorem member_143 : InMax4 r231 :=
  InMax4.mul member_142 member_0 product_234

theorem member_144 : InMax4 r232 :=
  InMax4.mul member_143 member_52 product_235

theorem member_145 : InMax4 r233 :=
  InMax4.mul member_144 member_66 product_236

theorem member_146 : InMax4 r234 :=
  InMax4.mul member_145 member_31 product_237

theorem member_147 : InMax4 r235 :=
  InMax4.inv member_146 product_238

theorem member_148 : InMax4 r236 :=
  InMax4.mul member_6 member_12 product_239

theorem member_149 : InMax4 r237 :=
  InMax4.mul member_148 mem_max4V product_240

theorem member_150 : InMax4 r238 :=
  InMax4.mul member_149 mem_max4U product_241

theorem member_151 : InMax4 r239 :=
  InMax4.mul member_150 member_11 product_242

theorem member_152 : InMax4 r240 :=
  InMax4.mul member_151 member_6 product_243

theorem member_153 : InMax4 r241 :=
  InMax4.mul member_152 mem_max4U product_244

theorem member_154 : InMax4 r242 :=
  InMax4.mul member_153 member_52 product_245

theorem member_155 : InMax4 r243 :=
  InMax4.mul member_154 member_67 product_246

theorem member_156 : InMax4 r244 :=
  InMax4.mul member_155 member_128 product_247

theorem member_157 : InMax4 r245 :=
  InMax4.mul member_156 member_93 product_248

theorem member_158 : InMax4 r246 :=
  InMax4.inv member_157 product_249

theorem member_159 : InMax4 r247 :=
  InMax4.mul member_11 mem_max4U product_250

theorem member_160 : InMax4 r248 :=
  InMax4.mul member_159 member_12 product_251

theorem member_161 : InMax4 r249 :=
  InMax4.mul member_160 member_12 product_252

theorem member_162 : InMax4 r250 :=
  InMax4.mul member_161 mem_max4U product_253

theorem member_163 : InMax4 r251 :=
  InMax4.mul member_162 member_12 product_254

theorem member_164 : InMax4 r252 :=
  InMax4.mul member_163 mem_max4U product_255

theorem member_165 : InMax4 r253 :=
  InMax4.mul member_164 member_66 product_256

theorem member_166 : InMax4 r254 :=
  InMax4.mul member_165 member_30 product_257

theorem member_167 : InMax4 r255 :=
  InMax4.mul member_166 member_52 product_258

theorem member_168 : InMax4 r256 :=
  InMax4.mul member_167 member_31 product_259

theorem member_169 : InMax4 r257 :=
  InMax4.mul member_168 member_98 product_260

theorem member_170 : InMax4 r258 :=
  InMax4.mul member_5 member_0 product_261

theorem member_171 : InMax4 r259 :=
  InMax4.mul member_170 member_5 product_262

theorem member_172 : InMax4 r260 :=
  InMax4.mul member_171 member_0 product_263

theorem member_173 : InMax4 r261 :=
  InMax4.mul member_172 member_5 product_264

theorem member_174 : InMax4 r262 :=
  InMax4.mul member_173 member_0 product_265

theorem member_175 : InMax4 r263 :=
  InMax4.mul member_174 member_66 product_266

theorem member_176 : InMax4 r264 :=
  InMax4.mul member_175 member_52 product_267

theorem member_177 : InMax4 r265 :=
  InMax4.mul member_176 member_67 product_268

theorem member_178 : InMax4 r266 :=
  InMax4.mul member_177 member_31 product_269

theorem member_179 : InMax4 r267 :=
  InMax4.mul member_178 member_98 product_270

theorem member_180 : InMax4 r268 :=
  InMax4.mul member_179 member_93 product_271

theorem member_181 : InMax4 r269 :=
  InMax4.inv member_180 product_272

theorem member_182 : InMax4 r270 :=
  InMax4.mul mem_max4V member_6 product_273

theorem member_183 : InMax4 r271 :=
  InMax4.mul member_182 mem_max4U product_274

theorem member_184 : InMax4 r272 :=
  InMax4.mul member_183 member_0 product_275

theorem member_185 : InMax4 r273 :=
  InMax4.mul member_184 member_5 product_276

theorem member_186 : InMax4 r274 :=
  InMax4.mul member_185 member_5 product_277

theorem member_187 : InMax4 r275 :=
  InMax4.mul member_186 member_12 product_278

theorem member_188 : InMax4 r276 :=
  InMax4.mul member_187 mem_max4U product_279

theorem member_189 : InMax4 r277 :=
  InMax4.mul member_188 member_52 product_280

theorem member_190 : InMax4 r278 :=
  InMax4.mul member_189 member_31 product_281

theorem member_191 : InMax4 r279 :=
  InMax4.mul member_190 member_31 product_282

theorem member_192 : InMax4 r280 :=
  InMax4.mul member_191 member_128 product_283

theorem member_193 : InMax4 r281 :=
  InMax4.mul member_192 member_98 product_284

theorem member_194 : InMax4 r282 :=
  InMax4.mul member_193 member_84 product_285

theorem member_195 : InMax4 r283 :=
  InMax4.mul mem_max4V member_11 product_286

theorem member_196 : InMax4 r284 :=
  InMax4.mul member_195 mem_max4V product_287

theorem member_197 : InMax4 r285 :=
  InMax4.mul member_196 member_11 product_288

theorem member_198 : InMax4 r286 :=
  InMax4.mul member_197 member_0 product_289

theorem member_199 : InMax4 r287 :=
  InMax4.mul member_198 member_0 product_290

theorem member_200 : InMax4 r288 :=
  InMax4.mul member_199 member_52 product_291

theorem member_201 : InMax4 r289 :=
  InMax4.mul member_200 member_31 product_292

theorem member_202 : InMax4 r290 :=
  InMax4.mul member_201 member_128 product_293

theorem member_203 : InMax4 r291 :=
  InMax4.mul member_202 member_98 product_294

theorem member_204 : InMax4 r292 :=
  InMax4.mul member_203 member_84 product_295

theorem member_205 : InMax4 r293 :=
  InMax4.mul member_12 member_6 product_296

theorem member_206 : InMax4 r294 :=
  InMax4.mul member_205 member_12 product_297

theorem member_207 : InMax4 r295 :=
  InMax4.mul member_206 mem_max4U product_298

theorem member_208 : InMax4 r296 :=
  InMax4.mul member_207 member_6 product_299

theorem member_209 : InMax4 r297 :=
  InMax4.mul member_208 mem_max4U product_300

theorem member_210 : InMax4 r298 :=
  InMax4.mul member_209 member_66 product_301

theorem member_211 : InMax4 r299 :=
  InMax4.mul member_210 member_31 product_302

theorem member_212 : InMax4 r300 :=
  InMax4.mul member_211 member_67 product_303

theorem member_213 : InMax4 r301 :=
  InMax4.mul member_212 member_31 product_304

theorem member_214 : InMax4 r302 :=
  InMax4.mul member_213 member_128 product_305

theorem member_215 : InMax4 r303 :=
  InMax4.mul member_214 member_98 product_306

theorem member_216 : InMax4 r304 :=
  InMax4.inv member_215 product_307

theorem member_217 : InMax4 r305 :=
  InMax4.mul member_11 member_6 product_308

theorem member_218 : InMax4 r306 :=
  InMax4.mul member_217 member_6 product_309

theorem member_219 : InMax4 r307 :=
  InMax4.mul member_218 member_6 product_310

theorem member_220 : InMax4 r308 :=
  InMax4.mul member_219 member_6 product_311

theorem member_221 : InMax4 r309 :=
  InMax4.mul member_220 mem_max4V product_312

theorem member_222 : InMax4 r310 :=
  InMax4.mul member_221 mem_max4U product_313

theorem member_223 : InMax4 r311 :=
  InMax4.mul member_222 member_53 product_314

theorem member_224 : InMax4 r312 :=
  InMax4.mul member_223 member_66 product_315

theorem member_225 : InMax4 r313 :=
  InMax4.mul member_224 member_31 product_316

theorem member_226 : InMax4 r314 :=
  InMax4.mul member_225 member_98 product_317

theorem member_227 : InMax4 r315 :=
  InMax4.inv member_226 product_318

theorem member_228 : InMax4 r316 :=
  InMax4.mul member_6 member_0 product_319

theorem member_229 : InMax4 r317 :=
  InMax4.mul member_228 member_6 product_320

theorem member_230 : InMax4 r318 :=
  InMax4.mul member_229 member_12 product_321

theorem member_231 : InMax4 r319 :=
  InMax4.mul member_230 mem_max4U product_322

theorem member_232 : InMax4 r320 :=
  InMax4.mul member_231 member_12 product_323

theorem member_233 : InMax4 r321 :=
  InMax4.mul member_232 mem_max4U product_324

theorem member_234 : InMax4 r322 :=
  InMax4.mul member_233 member_66 product_325

theorem member_235 : InMax4 r323 :=
  InMax4.mul member_234 member_30 product_326

theorem member_236 : InMax4 r324 :=
  InMax4.mul member_235 member_128 product_327

theorem member_237 : InMax4 r325 :=
  InMax4.mul member_236 member_84 product_328

theorem member_238 : InMax4 r326 :=
  InMax4.inv member_237 product_329

theorem member_239 : InMax4 r327 :=
  InMax4.mul member_6 mem_max4U product_330

theorem member_240 : InMax4 r328 :=
  InMax4.mul member_239 member_11 product_331

theorem member_241 : InMax4 r329 :=
  InMax4.mul member_240 member_0 product_332

theorem member_242 : InMax4 r330 :=
  InMax4.mul member_241 mem_max4U product_333

theorem member_243 : InMax4 r331 :=
  InMax4.mul member_242 member_12 product_334

theorem member_244 : InMax4 r332 :=
  InMax4.mul member_243 mem_max4V product_335

theorem member_245 : InMax4 r333 :=
  InMax4.mul member_244 member_31 product_336

theorem member_246 : InMax4 r334 :=
  InMax4.mul member_245 member_67 product_337

theorem member_247 : InMax4 r335 :=
  InMax4.mul member_246 member_31 product_338

theorem member_248 : InMax4 r336 :=
  InMax4.mul member_247 member_31 product_339

theorem member_249 : InMax4 r337 :=
  InMax4.mul member_248 member_98 product_340

theorem member_250 : InMax4 r338 :=
  InMax4.mul member_249 member_93 product_341

theorem member_251 : InMax4 r339 :=
  InMax4.inv member_250 product_342

theorem member_252 : InMax4 r340 :=
  InMax4.mul member_218 member_12 product_343

theorem member_253 : InMax4 r341 :=
  InMax4.mul member_252 mem_max4U product_344

theorem member_254 : InMax4 r342 :=
  InMax4.mul member_253 mem_max4V product_345

theorem member_255 : InMax4 r343 :=
  InMax4.mul member_254 member_67 product_346

theorem member_256 : InMax4 r344 :=
  InMax4.mul member_255 member_53 product_347

theorem member_257 : InMax4 r345 :=
  InMax4.mul member_256 member_67 product_348

theorem member_258 : InMax4 r346 :=
  InMax4.mul member_257 member_31 product_349

theorem member_259 : InMax4 r347 :=
  InMax4.inv member_258 product_350

theorem member_260 : InMax4 r348 :=
  InMax4.mul member_4 member_6 product_351

theorem member_261 : InMax4 r349 :=
  InMax4.mul member_260 mem_max4V product_352

theorem member_262 : InMax4 r350 :=
  InMax4.mul member_261 member_5 product_353

theorem member_263 : InMax4 r351 :=
  InMax4.mul member_262 member_12 product_354

theorem member_264 : InMax4 r352 :=
  InMax4.mul member_263 member_31 product_355

theorem member_265 : InMax4 r353 :=
  InMax4.mul member_264 member_31 product_356

theorem member_266 : InMax4 r354 :=
  InMax4.mul member_265 member_128 product_357

theorem member_267 : InMax4 r355 :=
  InMax4.mul member_266 member_84 product_358

theorem member_268 : InMax4 r356 :=
  InMax4.inv member_267 product_359

theorem member_269 : InMax4 r357 :=
  InMax4.mul member_10 member_12 product_360

theorem member_270 : InMax4 r358 :=
  InMax4.mul member_269 member_6 product_361

theorem member_271 : InMax4 r359 :=
  InMax4.mul member_270 member_0 product_362

theorem member_272 : InMax4 r360 :=
  InMax4.mul member_271 member_12 product_363

theorem member_273 : InMax4 r361 :=
  InMax4.mul member_272 member_31 product_364

theorem member_274 : InMax4 r362 :=
  InMax4.mul member_273 member_66 product_365

theorem member_275 : InMax4 r363 :=
  InMax4.mul member_274 member_30 product_366

theorem member_276 : InMax4 r364 :=
  InMax4.mul member_275 member_98 product_367

theorem member_277 : InMax4 r365 :=
  InMax4.mul member_276 member_93 product_368

theorem member_278 : InMax4 r366 :=
  InMax4.mul member_277 member_84 product_369

theorem member_279 : InMax4 r367 :=
  InMax4.inv member_278 product_370

theorem member_280 : InMax4 r31 :=
  InMax4.mul member_15 mem_max4U product_33

theorem member_281 : InMax4 r32 :=
  InMax4.mul member_280 member_280 product_34

theorem member_282 : InMax4 r33 :=
  InMax4.mul member_281 member_280 product_371

theorem member_283 : InMax4 r34 :=
  InMax4.mul member_282 member_282 product_36

theorem member_284 : InMax4 r35 :=
  InMax4.mul member_281 member_281 product_37

theorem member_285 : InMax4 r368 :=
  InMax4.mul member_284 member_284 product_372

theorem member_286 : InMax4 r38 :=
  InMax4.mul member_285 member_280 product_373

theorem member_287 : InMax4 r369 :=
  InMax4.mul mem_max4U member_283 product_374

theorem member_288 : InMax4 r370 :=
  InMax4.mul member_0 member_283 product_375

theorem member_289 : InMax4 r371 :=
  InMax4.mul member_288 mem_max4V product_376

theorem member_290 : InMax4 r372 :=
  InMax4.mul mem_max4U member_289 product_377

theorem member_291 : InMax4 r373 :=
  InMax4.mul member_290 mem_max4U product_378

theorem member_292 : InMax4 r374 :=
  InMax4.mul member_0 member_289 product_379

theorem member_293 : InMax4 r375 :=
  InMax4.mul member_292 mem_max4V product_380

theorem member_294 : InMax4 r376 :=
  InMax4.mul mem_max4U member_291 product_381

theorem member_295 : InMax4 r377 :=
  InMax4.mul member_0 member_291 product_382

theorem member_296 : InMax4 r378 :=
  InMax4.mul mem_max4U member_293 product_383

theorem member_297 : InMax4 r379 :=
  InMax4.mul member_296 mem_max4U product_384

theorem member_298 : InMax4 r380 :=
  InMax4.mul member_0 member_293 product_385

theorem member_299 : InMax4 r381 :=
  InMax4.mul member_298 mem_max4V product_386

theorem member_300 : InMax4 r382 :=
  InMax4.mul mem_max4U member_297 product_387

theorem member_301 : InMax4 r383 :=
  InMax4.mul member_0 member_297 product_388

theorem member_302 : InMax4 r384 :=
  InMax4.mul member_301 mem_max4V product_389

theorem member_303 : InMax4 r385 :=
  InMax4.mul mem_max4U member_299 product_390

theorem member_304 : InMax4 r386 :=
  InMax4.mul member_0 member_299 product_391

theorem member_305 : InMax4 r387 :=
  InMax4.mul mem_max4U member_302 product_392

theorem member_306 : InMax4 r388 :=
  InMax4.mul member_0 member_302 product_393

theorem member_307 : InMax4 r390 :=
  InMax4.mul member_137 member_291 product_396

theorem member_308 : InMax4 r393 :=
  InMax4.mul member_147 member_299 product_399

theorem member_309 : InMax4 r398 :=
  InMax4.mul member_169 member_297 product_404

theorem member_310 : InMax4 r403 :=
  InMax4.mul member_194 member_302 product_409

theorem member_311 : InMax4 r406 :=
  InMax4.mul member_204 member_299 product_412

theorem member_312 : InMax4 r413 :=
  InMax4.mul member_238 member_302 product_419

theorem member_313 : InMax4 r416 :=
  InMax4.mul member_251 member_289 product_422

theorem member_314 : InMax4 r419 :=
  InMax4.mul member_259 member_293 product_425

theorem member_315 : InMax4 r422 :=
  InMax4.mul member_268 member_289 product_428

theorem member_316 : InMax4 r424 :=
  InMax4.mul member_279 member_291 product_431
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates
