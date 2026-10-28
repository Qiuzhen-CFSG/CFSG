module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Data
/-!
# Shared HS double-coset invariants

The existing Sylow word enumeration is identified with smaller packed rows.
The three generators preserve the colors and selected source orbits on
ordered pairs. A checked decision tree recovers each representative from
its sixteen counts. Finally the intersection bounds yield the exact total
44,352,000. These are finite identities, proved by kernel computation.

Source: ATLAS HSG1-p100B0; Aschbacher--Smith A.3.12(18), pp.47--48.
The signature decoder is reproducible with `source/signature_decoder.py`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open Data EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData
set_option Elab.async false
private theorem packedMap_mod (n : ℕ) (p : Fin 100) : packedMap (n % 2^700) p = packedMap n p := by
  apply Fin.ext
  simp only [packedMap,Nat.shiftRight_eq_div_pow]
  have he : 2^700 = 2^(7*p.val) * 2^(700-7*p.val) := by
    rw [← pow_add]
    congr 1
    omega
  have hd : 128 ∣ 2^(700-7*p.val) := Nat.pow_dvd_pow 2 (by omega : 7 ≤ 700-7*p.val)
  rw [he,Nat.mod_mul_right_div_self,Nat.mod_mod_of_dvd _ hd]
set_option maxRecDepth 100000 in
private theorem sCode_block : ∀ (i : Fin 512), sCode i =
    (pointBlocks ⟨i.val / 32 % 16,Nat.mod_lt _ (by decide)⟩ >>> (700*(i.val%32))) % 2^700 := by
  apply allFin
  decide +kernel
theorem sylow_values (i : Fin 512) (p : Fin 100) : sVal i p = point i p := by
  unfold sVal
  rw [sCode_block,packedMap_mod]
  apply Fin.ext
  simp only [packedMap,point,← Nat.shiftRight_add]
  congr 3
  omega
set_option maxRecDepth 100000 in
theorem inverse_generator_values : ∀ (i : Fin 3) p,
    packedMap (siCode i) (sVal ⟨i.val+1,by omega⟩ p) = p := by
  apply allFin
  decide +kernel
set_option maxRecDepth 100000 in
theorem sylow_generator_values : ∀ (i : Fin 3) p,
    sVal ⟨i.val+1,by omega⟩ p = (sylowGenerator i : Equiv.Perm (Fin 100)) p := by
  apply allFin
  decide +kernel
set_option maxRecDepth 100000 in
theorem generator_color : ∀ (i : Fin 3) (x y : Fin 100),
    color (sVal ⟨i.val+1,by omega⟩ x,sVal ⟨i.val+1,by omega⟩ y) = color (x,y) := by
  apply allFin
  decide +kernel
set_option maxRecDepth 100000 in
private theorem generator_source_check : ∀ (i : Fin 3) (k : Fin 16),
    ((sourceList k).all fun x => decide (pairVal (sVal ⟨i.val+1,by omega⟩) x ∈ source k)) = true := by
  apply allFin
  decide +kernel

theorem generator_source (i : Fin 3) (k : Fin 16) (x : Point) (hx : x ∈ source k) :
    pairVal (sVal ⟨i.val+1,by omega⟩) x ∈ source k := by
  exact of_decide_eq_true (List.all_eq_true.mp (generator_source_check i k) x hx)
private def countDecoder (v : Fin 16 → ℕ) : Fin 270 := (if v 11 ≤ 0 then (if v 2 ≤ 0 then (if v 14 ≤ 1 then (if v 5 ≤ 0 then (if v 0 ≤ 0 then (if v 3 ≤ 0 then (if v 6 ≤ 2 then (if v 6 ≤ 0 then 110 else 16) else (if v 6 ≤ 4 then 4 else 0)) else (if v 1 ≤ 0 then (if v 3 ≤ 1 then 12 else 108) else 245)) else (if v 1 ≤ 0 then (if v 0 ≤ 1 then (if v 3 ≤ 0 then 236 else 231) else (if v 0 ≤ 2 then (if v 6 ≤ 2 then 10 else 6) else 187)) else (if v 0 ≤ 2 then (if v 0 ≤ 1 then 75 else 41) else (if v 9 ≤ 2 then 98 else 127)))) else (if v 1 ≤ 0 then (if v 0 ≤ 0 then (if v 3 ≤ 0 then 1 else (if v 3 ≤ 1 then (if v 5 ≤ 2 then 243 else 13) else 109)) else (if v 0 ≤ 1 then (if v 3 ≤ 0 then 74 else 233) else (if v 0 ≤ 2 then (if v 6 ≤ 0 then 47 else 40) else 155))) else (if v 0 ≤ 1 then (if v 0 ≤ 0 then (if v 1 ≤ 2 then (if v 3 ≤ 0 then 14 else 113) else 2) else 239) else (if v 9 ≤ 0 then (if v 1 ≤ 2 then 32 else 26) else (if v 1 ≤ 1 then 49 else 44))))) else (if v 5 ≤ 1 then (if v 14 ≤ 2 then (if v 6 ≤ 0 then (if v 0 ≤ 1 then (if v 1 ≤ 0 then 81 else 234) else (if v 0 ≤ 2 then 259 else 185)) else (if v 5 ≤ 0 then (if v 9 ≤ 1 then 148 else 160) else (if v 1 ≤ 0 then 166 else (if v 9 ≤ 1 then 92 else 89)))) else (if v 0 ≤ 3 then (if v 1 ≤ 0 then (if v 4 ≤ 0 then 165 else 157) else (if v 0 ≤ 2 then 262 else (if v 1 ≤ 1 then 125 else 163))) else (if v 1 ≤ 0 then (if v 7 ≤ 0 then 189 else 182) else (if v 9 ≤ 1 then 184 else 183)))) else (if v 15 ≤ 0 then (if v 3 ≤ 0 then (if v 6 ≤ 0 then (if v 0 ≤ 2 then 25 else 186) else (if v 6 ≤ 1 then 96 else 122)) else (if v 0 ≤ 2 then (if v 3 ≤ 1 then 261 else 263) else (if v 6 ≤ 0 then (if v 9 ≤ 2 then 86 else 121) else 87))) else (if v 15 ≤ 2 then (if v 0 ≤ 2 then (if v 1 ≤ 0 then 39 else 31) else (if v 0 ≤ 3 then (if v 3 ≤ 0 then 167 else 88) else 188)) else (if v 7 ≤ 0 then (if v 0 ≤ 1 then 232 else 151) else (if v 0 ≤ 3 then 123 else 181)))))) else (if v 6 ≤ 0 then (if v 13 ≤ 0 then (if v 5 ≤ 2 then (if v 0 ≤ 0 then (if v 1 ≤ 0 then (if v 2 ≤ 1 then 242 else 111) else (if v 12 ≤ 0 then 112 else 244)) else (if v 1 ≤ 1 then (if v 0 ≤ 2 then 260 else 120) else (if v 8 ≤ 0 then 97 else 128))) else (if v 1 ≤ 0 then (if v 0 ≤ 0 then (if v 2 ≤ 3 then 17 else 5) else (if v 2 ≤ 1 then 7 else 11)) else (if v 7 ≤ 0 then (if v 12 ≤ 0 then 43 else 34) else (if v 0 ≤ 2 then 36 else 94)))) else (if v 0 ≤ 2 then (if v 1 ≤ 0 then (if v 0 ≤ 0 then (if v 2 ≤ 1 then 241 else 240) else (if v 0 ≤ 1 then 237 else (if v 5 ≤ 1 then 258 else 37))) else (if v 2 ≤ 1 then (if v 14 ≤ 0 then 83 else 85) else (if v 0 ≤ 1 then (if v 7 ≤ 2 then 79 else 77) else 45))) else (if v 5 ≤ 2 then (if v 7 ≤ 0 then (if v 1 ≤ 0 then 95 else 150) else (if v 9 ≤ 1 then 159 else 149)) else (if v 1 ≤ 0 then (if v 9 ≤ 0 then 158 else 153) else (if v 7 ≤ 0 then 126 else 90))))) else (if v 14 ≤ 1 then (if v 2 ≤ 1 then (if v 5 ≤ 1 then (if v 0 ≤ 1 then (if v 15 ≤ 1 then 78 else 80) else (if v 0 ≤ 2 then 35 else (if v 1 ≤ 0 then 154 else 162))) else (if v 9 ≤ 1 then (if v 0 ≤ 1 then 82 else 8) else (if v 0 ≤ 2 then 28 else 147))) else (if v 0 ≤ 1 then (if v 0 ≤ 0 then (if v 1 ≤ 2 then 15 else 3) else (if v 3 ≤ 0 then 235 else 84)) else (if v 1 ≤ 1 then (if v 1 ≤ 0 then 38 else 50) else (if v 1 ≤ 2 then (if v 5 ≤ 0 then 33 else 42) else 27)))) else (if v 5 ≤ 1 then (if v 6 ≤ 1 then (if v 7 ≤ 0 then (if v 0 ≤ 1 then 238 else (if v 1 ≤ 0 then 156 else 164)) else (if v 9 ≤ 0 then 91 else 93)) else (if v 0 ≤ 2 then 46 else (if v 5 ≤ 0 then 152 else 124))) else (if v 2 ≤ 1 then (if v 6 ≤ 1 then (if v 0 ≤ 1 then 73 else 161) else (if v 8 ≤ 0 then 30 else 24)) else (if v 5 ≤ 2 then (if v 0 ≤ 1 then 76 else (if v 1 ≤ 1 then 51 else 9)) else (if v 1 ≤ 0 then 48 else 29))))))) else (if v 5 ≤ 0 then (if v 6 ≤ 0 then (if v 0 ≤ 2 then (if v 0 ≤ 1 then (if v 2 ≤ 0 then (if v 3 ≤ 0 then (if v 0 ≤ 0 then 116 else 103) else (if v 11 ≤ 2 then 249 else 115)) else (if v 2 ≤ 1 then (if v 3 ≤ 0 then 246 else 250) else (if v 11 ≤ 2 then 248 else 119))) else (if v 2 ≤ 0 then (if v 1 ≤ 0 then (if v 3 ≤ 1 then 216 else 266) else (if v 13 ≤ 0 then 214 else 204)) else (if v 4 ≤ 0 then (if v 3 ≤ 0 then 199 else 268) else (if v 13 ≤ 2 then 209 else 200)))) else (if v 0 ≤ 3 then (if v 14 ≤ 2 then (if v 8 ≤ 0 then (if v 10 ≤ 0 then 257 else 252) else 256) else (if v 7 ≤ 0 then 253 else (if v 8 ≤ 0 then 255 else 254))) else (if v 1 ≤ 0 then (if v 3 ≤ 0 then (if v 4 ≤ 0 then 226 else (if v 9 ≤ 0 then 230 else 228)) else (if v 3 ≤ 1 then 142 else 129)) else (if v 1 ≤ 1 then (if v 3 ≤ 1 then 191 else 196) else (if v 8 ≤ 0 then 146 else 133))))) else (if v 3 ≤ 0 then (if v 0 ≤ 2 then (if v 0 ≤ 1 then (if v 0 ≤ 0 then (if v 7 ≤ 0 then 117 else 247) else (if v 2 ≤ 0 then 99 else (if v 7 ≤ 0 then 105 else 107))) else (if v 11 ≤ 1 then (if v 6 ≤ 1 then 198 else 18) else (if v 2 ≤ 0 then 265 else 264))) else (if v 9 ≤ 0 then (if v 0 ≤ 3 then (if v 6 ≤ 2 then 137 else 176) else (if v 10 ≤ 0 then 225 else 131)) else (if v 6 ≤ 1 then (if v 0 ≤ 3 then 135 else 143) else (if v 1 ≤ 0 then 172 else 56)))) else (if v 6 ≤ 1 then (if v 0 ≤ 2 then (if v 9 ≤ 0 then (if v 1 ≤ 0 then 207 else 205) else (if v 0 ≤ 1 then 101 else 213)) else (if v 1 ≤ 0 then (if v 0 ≤ 3 then 174 else 219) else (if v 9 ≤ 2 then 222 else 221))) else (if v 3 ≤ 1 then (if v 0 ≤ 0 then 251 else (if v 0 ≤ 2 then (if v 11 ≤ 1 then 22 else 269) else 139)) else (if v 0 ≤ 0 then (if v 6 ≤ 2 then 118 else 114) else (if v 0 ≤ 2 then 267 else 145)))))) else (if v 2 ≤ 0 then (if v 0 ≤ 3 then (if v 13 ≤ 0 then (if v 1 ≤ 0 then (if v 0 ≤ 2 then (if v 14 ≤ 2 then 206 else 208) else (if v 5 ≤ 2 then 177 else 138)) else (if v 5 ≤ 1 then (if v 3 ≤ 0 then 180 else (if v 9 ≤ 0 then 53 else 52)) else (if v 1 ≤ 1 then 54 else 140))) else (if v 1 ≤ 0 then (if v 0 ≤ 2 then (if v 13 ≤ 2 then 211 else 202) else (if v 9 ≤ 1 then 67 else 71)) else (if v 4 ≤ 0 then (if v 3 ≤ 0 then 55 else 64) else (if v 6 ≤ 0 then 169 else (if v 9 ≤ 1 then 58 else 62))))) else (if v 3 ≤ 0 then (if v 14 ≤ 2 then (if v 4 ≤ 1 then (if v 4 ≤ 0 then 224 else 192) else (if v 5 ≤ 1 then 229 else 144)) else (if v 6 ≤ 0 then (if v 4 ≤ 0 then 132 else 194) else (if v 4 ≤ 1 then 193 else 227))) else (if v 1 ≤ 0 then (if v 5 ≤ 1 then (if v 9 ≤ 2 then 218 else 220) else (if v 3 ≤ 1 then 141 else 130)) else (if v 3 ≤ 1 then (if v 5 ≤ 1 then 223 else 190) else (if v 1 ≤ 1 then 195 else 134))))) else (if v 1 ≤ 0 then (if v 0 ≤ 2 then (if v 5 ≤ 1 then (if v 3 ≤ 0 then (if v 13 ≤ 2 then 210 else 201) else (if v 9 ≤ 0 then 217 else 215)) else (if v 0 ≤ 1 then (if v 2 ≤ 1 then (if v 6 ≤ 0 then 106 else 100) else 104) else (if v 2 ≤ 1 then (if v 5 ≤ 2 then 197 else 19) else 23))) else (if v 4 ≤ 0 then (if v 3 ≤ 0 then (if v 6 ≤ 0 then 171 else 136) else (if v 9 ≤ 0 then 173 else 175)) else (if v 5 ≤ 1 then (if v 9 ≤ 0 then 72 else 68) else (if v 9 ≤ 1 then 69 else 70)))) else (if v 4 ≤ 0 then (if v 5 ≤ 1 then (if v 0 ≤ 2 then (if v 9 ≤ 0 then 212 else 203) else (if v 14 ≤ 1 then 66 else 65)) else (if v 2 ≤ 1 then (if v 0 ≤ 2 then 20 else 57) else (if v 0 ≤ 1 then 102 else 21))) else (if v 6 ≤ 1 then (if v 5 ≤ 1 then (if v 9 ≤ 1 then 178 else 170) else (if v 9 ≤ 0 then 61 else 59)) else (if v 7 ≤ 0 then (if v 9 ≤ 1 then 60 else 63) else (if v 9 ≤ 0 then 179 else 168))))))))

set_option maxRecDepth 100000 in
private theorem countDecoder_spec : ∀ i : Fin 270, countDecoder (countVal i) = i := by
  apply allFin
  decide +kernel

theorem count_values_injective (i j : Fin 270)
    (h : ∀ k : Fin 16, countVal i k = countVal j k) : i = j := by
  have he := congrArg countDecoder (funext h)
  simpa only [countDecoder_spec] using he

set_option maxRecDepth 100000 in
theorem bounds_positive : ∀ j, 0 < bound j := by
  apply allFin
  decide +kernel
set_option maxRecDepth 100000 in
theorem sizes_mul : ∀ j, lower j * bound j = 512 * 512 := by
  apply allFin
  decide +kernel
set_option maxRecDepth 100000 in
theorem sizes_sum : (∑ j : Fin 270, lower j) = 44352000 := by decide +kernel

end Sporadic.LeechRelated.HS.SylowOvergroups
