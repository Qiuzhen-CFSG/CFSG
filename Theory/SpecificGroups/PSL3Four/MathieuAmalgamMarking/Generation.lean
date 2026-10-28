module

public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Matrices

/-! Untrusted finite word witnesses. Every one of the16 translations and60
lower-right determinant-one blocks is checked in Lean's kernel. -/

namespace Matrix.PSL3Four.MathieuAmalgamMarking
open Subgroup.CosetWordCertificate
open scoped Matrix
private def branch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

private def translationCode : Nat → Nat :=
  (branch 8 (branch 4 (branch 2 (branch 1 (fun _ => 0) (fun _ => 6591666)) (branch 3 (fun _ => 341) (fun _ => 7258541))) (branch 6 (branch 5 (fun _ => 211666) (fun _ => 18)) (branch 7 (fun _ => 227291) (fun _ => 217)))) (branch 12 (branch 10 (branch 9 (fun _ => 11083) (fun _ => 6513541)) (branch 11 (fun _ => 8466791) (fun _ => 149167))) (branch 14 (branch 13 (fun _ => 133542) (fun _ => 14208)) (branch 15 (fun _ => 6588666) (fun _ => 6513666)))))

private def blockCode : Nat → Nat :=
  (branch 128 (branch 64 (branch 32 (branch 16 (branch 8 (branch 4 (branch 2 (branch 1 (fun _ => 0) (fun _ => 0)) (branch 3 (fun _ => 0) (fun _ => 0))) (branch 6 (branch 5 (fun _ => 0) (fun _ => 0)) (branch 7 (fun _ => 0) (fun _ => 0)))) (branch 12 (branch 10 (branch 9 (fun _ => 0) (fun _ => 0)) (branch 11 (fun _ => 0) (fun _ => 0))) (branch 14 (branch 13 (fun _ => 0) (fun _ => 0)) (branch 15 (fun _ => 0) (fun _ => 0))))) (branch 24 (branch 20 (branch 18 (branch 17 (fun _ => 0) (fun _ => 0)) (branch 19 (fun _ => 0) (fun _ => 0))) (branch 22 (branch 21 (fun _ => 669946) (fun _ => 339316)) (branch 23 (fun _ => 276817) (fun _ => 338668)))) (branch 28 (branch 26 (branch 25 (fun _ => 0) (fun _ => 0)) (branch 27 (fun _ => 0) (fun _ => 0))) (branch 30 (branch 29 (fun _ => 0) (fun _ => 0)) (branch 31 (fun _ => 0) (fun _ => 0)))))) (branch 48 (branch 40 (branch 36 (branch 34 (branch 33 (fun _ => 0) (fun _ => 0)) (branch 35 (fun _ => 0) (fun _ => 0))) (branch 38 (branch 37 (fun _ => 0) (fun _ => 0)) (branch 39 (fun _ => 0) (fun _ => 0)))) (branch 44 (branch 42 (branch 41 (fun _ => 0) (fun _ => 0)) (branch 43 (fun _ => 0) (fun _ => 0))) (branch 46 (branch 45 (fun _ => 261072) (fun _ => 13542)) (branch 47 (fun _ => 55364) (fun _ => 208458))))) (branch 56 (branch 52 (branch 50 (branch 49 (fun _ => 0) (fun _ => 0)) (branch 51 (fun _ => 0) (fun _ => 0))) (branch 54 (branch 53 (fun _ => 0) (fun _ => 0)) (branch 55 (fun _ => 0) (fun _ => 0)))) (branch 60 (branch 58 (branch 57 (fun _ => 357946) (fun _ => 11171)) (branch 59 (fun _ => 2709) (fun _ => 148963))) (branch 62 (branch 61 (fun _ => 0) (fun _ => 0)) (branch 63 (fun _ => 0) (fun _ => 0))))))) (branch 96 (branch 80 (branch 72 (branch 68 (branch 66 (branch 65 (fun _ => 0) (fun _ => 0)) (branch 67 (fun _ => 0) (fun _ => 0))) (branch 70 (branch 69 (fun _ => 0) (fun _ => 276046)) (branch 71 (fun _ => 0) (fun _ => 0)))) (branch 76 (branch 74 (branch 73 (fun _ => 0) (fun _ => 745416)) (branch 75 (fun _ => 0) (fun _ => 0))) (branch 78 (branch 77 (fun _ => 0) (fun _ => 354922)) (branch 79 (fun _ => 0) (fun _ => 0))))) (branch 88 (branch 84 (branch 82 (branch 81 (fun _ => 0) (fun _ => 260542)) (branch 83 (fun _ => 0) (fun _ => 0))) (branch 86 (branch 85 (fun _ => 223988) (fun _ => 0)) (branch 87 (fun _ => 0) (fun _ => 0)))) (branch 92 (branch 90 (branch 89 (fun _ => 0) (fun _ => 0)) (branch 91 (fun _ => 0) (fun _ => 571))) (branch 94 (branch 93 (fun _ => 0) (fun _ => 0)) (branch 95 (fun _ => 68484) (fun _ => 0)))))) (branch 112 (branch 104 (branch 100 (branch 98 (branch 97 (fun _ => 0) (fun _ => 1305838)) (branch 99 (fun _ => 0) (fun _ => 0))) (branch 102 (branch 101 (fun _ => 0) (fun _ => 0)) (branch 103 (fun _ => 0) (fun _ => 45441)))) (branch 108 (branch 106 (branch 105 (fun _ => 0) (fun _ => 0)) (branch 107 (fun _ => 11197) (fun _ => 0))) (branch 110 (branch 109 (fun _ => 5988) (fun _ => 0)) (branch 111 (fun _ => 0) (fun _ => 0))))) (branch 120 (branch 116 (branch 114 (branch 113 (fun _ => 0) (fun _ => 276072)) (branch 115 (fun _ => 0) (fun _ => 0))) (branch 118 (branch 117 (fun _ => 0) (fun _ => 0)) (branch 119 (fun _ => 1071) (fun _ => 0)))) (branch 124 (branch 122 (branch 121 (fun _ => 8459) (fun _ => 0)) (branch 123 (fun _ => 0) (fun _ => 0))) (branch 126 (branch 125 (fun _ => 0) (fun _ => 0)) (branch 127 (fun _ => 0) (fun _ => 264208)))))))) (branch 192 (branch 160 (branch 144 (branch 136 (branch 132 (branch 130 (branch 129 (fun _ => 0) (fun _ => 0)) (branch 131 (fun _ => 0) (fun _ => 10566))) (branch 134 (branch 133 (fun _ => 0) (fun _ => 0)) (branch 135 (fun _ => 0) (fun _ => 70983)))) (branch 140 (branch 138 (branch 137 (fun _ => 0) (fun _ => 0)) (branch 139 (fun _ => 0) (fun _ => 44817))) (branch 142 (branch 141 (fun _ => 0) (fun _ => 0)) (branch 143 (fun _ => 0) (fun _ => 43))))) (branch 152 (branch 148 (branch 146 (branch 145 (fun _ => 0) (fun _ => 0)) (branch 147 (fun _ => 0) (fun _ => 26818))) (branch 150 (branch 149 (fun _ => 145859) (fun _ => 0)) (branch 151 (fun _ => 0) (fun _ => 0)))) (branch 156 (branch 154 (branch 153 (fun _ => 0) (fun _ => 0)) (branch 155 (fun _ => 263566) (fun _ => 0))) (branch 158 (branch 157 (fun _ => 0) (fun _ => 55213)) (branch 159 (fun _ => 0) (fun _ => 0)))))) (branch 176 (branch 168 (branch 164 (branch 162 (branch 161 (fun _ => 0) (fun _ => 0)) (branch 163 (fun _ => 0) (fun _ => 29921))) (branch 166 (branch 165 (fun _ => 0) (fun _ => 0)) (branch 167 (fun _ => 261046) (fun _ => 0)))) (branch 172 (branch 170 (branch 169 (fun _ => 0) (fun _ => 14318)) (branch 171 (fun _ => 0) (fun _ => 0))) (branch 174 (branch 173 (fun _ => 52109) (fun _ => 0)) (branch 175 (fun _ => 0) (fun _ => 0))))) (branch 184 (branch 180 (branch 178 (branch 177 (fun _ => 0) (fun _ => 0)) (branch 179 (fun _ => 0) (fun _ => 27208))) (branch 182 (branch 181 (fun _ => 0) (fun _ => 1672)) (branch 183 (fun _ => 0) (fun _ => 0)))) (branch 188 (branch 186 (branch 185 (fun _ => 2238) (fun _ => 0)) (branch 187 (fun _ => 0) (fun _ => 0))) (branch 190 (branch 189 (fun _ => 0) (fun _ => 0)) (branch 191 (fun _ => 8482316) (fun _ => 0))))))) (branch 224 (branch 208 (branch 200 (branch 196 (branch 194 (branch 193 (fun _ => 0) (fun _ => 0)) (branch 195 (fun _ => 8964) (fun _ => 0))) (branch 198 (branch 197 (fun _ => 0) (fun _ => 0)) (branch 199 (fun _ => 70858) (fun _ => 0)))) (branch 204 (branch 202 (branch 201 (fun _ => 0) (fun _ => 0)) (branch 203 (fun _ => 29316) (fun _ => 0))) (branch 206 (branch 205 (fun _ => 0) (fun _ => 0)) (branch 207 (fun _ => 92) (fun _ => 0))))) (branch 216 (branch 212 (branch 210 (branch 209 (fun _ => 0) (fun _ => 0)) (branch 211 (fun _ => 57297) (fun _ => 0))) (branch 214 (branch 213 (fun _ => 289738) (fun _ => 0)) (branch 215 (fun _ => 0) (fun _ => 0)))) (branch 220 (branch 218 (branch 217 (fun _ => 0) (fun _ => 333)) (branch 219 (fun _ => 0) (fun _ => 0))) (branch 222 (branch 221 (fun _ => 0) (fun _ => 0)) (branch 223 (fun _ => 0) (fun _ => 1395983)))))) (branch 240 (branch 232 (branch 228 (branch 226 (branch 225 (fun _ => 0) (fun _ => 0)) (branch 227 (fun _ => 42292) (fun _ => 0))) (branch 230 (branch 229 (fun _ => 0) (fun _ => 44916)) (branch 231 (fun _ => 0) (fun _ => 0)))) (branch 236 (branch 234 (branch 233 (fun _ => 0) (fun _ => 0)) (branch 235 (fun _ => 0) (fun _ => 654166))) (branch 238 (branch 237 (fun _ => 357446) (fun _ => 0)) (branch 239 (fun _ => 0) (fun _ => 0))))) (branch 248 (branch 244 (branch 242 (branch 241 (fun _ => 0) (fun _ => 0)) (branch 243 (fun _ => 70966) (fun _ => 0))) (branch 246 (branch 245 (fun _ => 0) (fun _ => 0)) (branch 247 (fun _ => 0) (fun _ => 651816)))) (branch 252 (branch 250 (branch 249 (fun _ => 342417) (fun _ => 0)) (branch 251 (fun _ => 0) (fun _ => 0))) (branch 254 (branch 253 (fun _ => 0) (fun _ => 341666)) (branch 255 (fun _ => 0) (fun _ => 0)))))))))

private def unpackWord (n : Nat) : Word (Fin 2) :=
  if n = 0 then [] else
    (⟨((n % 5 - 1) / 2) % 2, Nat.mod_lt _ (by decide)⟩, (n % 5 - 1) % 2 == 0) ::
      unpackWord (n / 5)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

private def fieldCode (x : NativeF) : Nat := x.re.val + 2*x.im.val
private def translationWord (x y : NativeF) : Word (Fin 2) :=
  unpackWord (translationCode (fieldCode x + 4*fieldCode y))
private def blockWord (v : Fin 4 → NativeF) : Word (Fin 2) :=
  unpackWord (blockCode (fieldCode (v 0)+4*fieldCode (v 1)+16*fieldCode (v 2)+64*fieldCode (v 3)))

set_option maxRecDepth 4096 in
private theorem translationWord_checked : ∀ x y : NativeF,
    (eval nativePair (translationWord x y)).val = !![1,x,y;0,1,0;0,0,1] := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem blockWord_checked : ∀ v : Fin 4 → NativeF,
    v 0*v 3-v 1*v 2=1 →
    (eval nativePair (blockWord v)).val = !![1,0,0;0,v 0,v 1;0,v 2,v 3] := by
  decide +kernel

private theorem eval_mem {G α : Type*} [Group G] (g : α → G) (w : Word α) :
    eval g w ∈ Subgroup.closure (Set.range g) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply Subgroup.mul_mem _ _ ih
    split
    · exact Subgroup.subset_closure (Set.mem_range_self _)
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self _))

public theorem native_pair_generates : Subgroup.closure (Set.range nativePair) =
    Matrix.PSL3.LinearThree.pointLocalSL NativeF := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact nativePair_mem i
  · intro g hg
    have hs := (Matrix.PSL3.LinearThree.mem_pointLocalSL_iff NativeF g).mp hg
    let v : Fin 4 → NativeF := ![g.val 1 1,g.val 1 2,g.val 2 1,g.val 2 2]
    have hv : v 0*v 3-v 1*v 2=1 := by
      have hd : g.val.det = 1 := g.property
      rw [Matrix.det_fin_three] at hd
      simpa [hs.1,hs.2.1,hs.2.2,v] using hd
    have he : g = eval nativePair (blockWord v) *
        eval nativePair (translationWord (g.val 0 1) (g.val 0 2)) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul,blockWord_checked v hv,translationWord_checked]
      funext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Fin.sum_univ_three,v,hs.1,hs.2.1,hs.2.2]
    rw [he]
    exact Subgroup.mul_mem _ (eval_mem _ _) (eval_mem _ _)
end Matrix.PSL3Four.MathieuAmalgamMarking
