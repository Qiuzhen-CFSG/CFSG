module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.FiniteModel.EnumerationData
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.FinCases
/-!
# Certified enumeration of the first nonsplit Held model

The four-point decoder proves that the rows of `EnumerationData` are distinct.
The checked predecessor and transition tables prove, respectively, that every
row belongs to the generated subgroup and that the rows exhaust it. Thus
`enumeration` is an equivalence with the actual carrier `NonsplitModels.First`.
The power identities use its inherited permutation multiplication; no alternate
group law or unproved model identification is introduced.

Source problem: Huppert--Blackburn III, XII.1.18(b), p.314, citing Held,
J. Algebra 8 (1968), 436--449, DOI 10.1016/0021-8693(68)90054-9.
-/

@[expose] public section
namespace Theory.GroupTheory.HeldM22A10.FirstExclusion.FiniteModel
open NonsplitModels
set_option maxRecDepth 10000
private def decodeKey (n : ℕ) : Index :=
  (if n < 32844 then (if n < 16584 then (if n < 9356 then (if n < 5593 then (if n < 2756 then (if n < 1708 then (if n < 1198 then (if n < 1166 then 219 else (if n < 1196 then 321 else 326)) else (if n < 1676 then 379 else (if n < 1678 then 309 else 276))) else (if n < 2246 then (if n < 1710 then 280 else (if n < 2244 then 334 else 222)) else (if n < 2276 then 156 else (if n < 2278 then 187 else 233)))) else (if n < 3176 then (if n < 2790 then (if n < 2758 then 346 else (if n < 2788 then 214 else 278)) else (if n < 3144 then 312 else (if n < 3146 then 252 else 184))) else (if n < 3658 then (if n < 3178 then 347 else (if n < 3656 then 229 else 191)) else (if n < 3688 then 255 else (if n < 3690 then 238 else 316))))) else (if n < 7005 then (if n < 6137 then (if n < 5627 then (if n < 5595 then 308 else (if n < 5625 then 69 else 105)) else (if n < 6105 then 142 else (if n < 6107 then 82 else 122))) else (if n < 6495 then (if n < 6139 then 138 else (if n < 6493 then 109 else 57)) else (if n < 6525 then 277 else (if n < 6527 then 76 else 323)))) else (if n < 7605 then (if n < 7039 then (if n < 7007 then 101 else (if n < 7037 then 314 else 135)) else (if n < 7573 then 216 else (if n < 7575 then 126 else 237))) else (if n < 8087 then (if n < 7607 then 231 else (if n < 8085 then 185 else 211)) else (if n < 8117 then 131 else (if n < 8119 then 152 else 370)))))) else (if n < 13785 then (if n < 10948 then (if n < 9900 then (if n < 9390 then (if n < 9358 then 52 else (if n < 9388 then 259 else 367)) else (if n < 9868 then 319 else (if n < 9870 then 71 else 121))) else (if n < 10438 then (if n < 9902 then 146 else (if n < 10436 then 81 else 150)) else (if n < 10468 then 245 else (if n < 10470 then 243 else 32)))) else (if n < 11368 then (if n < 10982 then (if n < 10950 then 209 else (if n < 10980 then 297 else 134)) else (if n < 11336 then 20 else (if n < 11338 then 41 else 64))) else (if n < 11850 then (if n < 11370 then 226 else (if n < 11848 then 158 else 267)) else (if n < 11880 then 36 else (if n < 11882 then 299 else 26))))) else (if n < 15197 then (if n < 14329 then (if n < 13819 then (if n < 13787 then 62 else (if n < 13817 then 113 else 12)) else (if n < 14297 then 360 else (if n < 14299 then 172 else 98))) else (if n < 14687 then (if n < 14331 then 352 else (if n < 14685 then 7 else 93)) else (if n < 14717 then 50 else (if n < 14719 then 290 else 89)))) else (if n < 15797 then (if n < 15231 then (if n < 15199 then 284 else (if n < 15229 then 350 else 5)) else (if n < 15765 then 31 else (if n < 15767 then 15 else 341))) else (if n < 16279 then (if n < 15799 then 45 else (if n < 16277 then 25 else 176)) else (if n < 16309 then 196 else (if n < 16311 then 201 else 118))))))) else (if n < 24776 then (if n < 20893 then (if n < 18956 then (if n < 17128 then (if n < 16618 then (if n < 16586 then 202 else (if n < 16616 then 289 else 46)) else (if n < 17096 then 86 else (if n < 17098 then 337 else 264))) else (if n < 18446 then (if n < 17130 then 364 else (if n < 18444 then 127 else 67)) else (if n < 18476 then 164 else (if n < 18478 then 111 else 262)))) else (if n < 19616 then (if n < 18990 then (if n < 18958 then 295 else (if n < 18988 then 257 else 23)) else (if n < 19584 then 116 else (if n < 19586 then 61 else 157))) else (if n < 20098 then (if n < 19618 then 162 else (if n < 20096 then 90 else 11)) else (if n < 20128 then 227 else (if n < 20130 then 359 else 141))))) else (if n < 23505 then (if n < 21437 then (if n < 20927 then (if n < 20895 then 1 else (if n < 20925 then 234 else 215)) else (if n < 21405 then 304 else (if n < 21407 then 246 else 33))) else (if n < 22995 then (if n < 21439 then 38 else (if n < 22993 then 21 else 43)) else (if n < 23025 then 80 else (if n < 23027 then 75 else 307)))) else (if n < 23865 then (if n < 23539 then (if n < 23507 then 66 else (if n < 23537 then 120 else 330)) else (if n < 23833 then 4 else (if n < 23835 then 10 else 16))) else (if n < 24347 then (if n < 23867 then 232 else (if n < 24345 then 140 else 208)) else (if n < 24377 then 148 else (if n < 24379 then 125 else 85)))))) else (if n < 29085 then (if n < 27148 then (if n < 25320 then (if n < 24810 then (if n < 24778 then 343 else (if n < 24808 then 270 else 268)) else (if n < 25288 then 178 else (if n < 25290 then 378 else 339))) else (if n < 26638 then (if n < 25322 then 345 else (if n < 26636 then 103 else 190)) else (if n < 26668 then 355 else (if n < 26670 then 266 else 175)))) else (if n < 27808 then (if n < 27182 then (if n < 27150 then 273 else (if n < 27180 then 344 else 171)) else (if n < 27776 then 275 else (if n < 27778 then 183 else 272))) else (if n < 28290 then (if n < 27810 then 97 else (if n < 28288 then 342 else 351)) else (if n < 28320 then 180 else (if n < 28322 then 168 else 108))))) else (if n < 31697 then (if n < 29629 then (if n < 29119 then (if n < 29087 then 223 else (if n < 29117 then 188 else 47)) else (if n < 29597 then 203 else (if n < 29599 then 285 else 220))) else (if n < 31187 then (if n < 29631 then 28 else (if n < 31185 then 177 else 271)) else (if n < 31217 then 292 else (if n < 31219 then 56 else 92)))) else (if n < 32057 then (if n < 31731 then (if n < 31699 then 313 else (if n < 31729 then 258 else 354)) else (if n < 32025 then 51 else (if n < 32027 then 99 else 167))) else (if n < 32539 then (if n < 32059 then 186 else (if n < 32537 then 107 else 338)) else (if n < 32569 then 197 else (if n < 32571 then 372 else 132)))))))) else (if n < 49284 then (if n < 41036 then (if n < 37333 then (if n < 34496 then (if n < 33388 then (if n < 32878 then (if n < 32846 then 78 else (if n < 32876 then 173 else 165)) else (if n < 33356 then 261 else (if n < 33358 then 139 else 83))) else (if n < 33986 then (if n < 33390 then 106 else (if n < 33984 then 328 else 205)) else (if n < 34016 then 340 else (if n < 34018 then 49 else 265)))) else (if n < 35876 then (if n < 34530 then (if n < 34498 then 153 else (if n < 34528 then 250 else 88)) else (if n < 35844 then 145 else (if n < 35846 then 241 else 42))) else (if n < 36358 then (if n < 35878 then 161 else (if n < 36356 then 96 else 55)) else (if n < 36388 then 74 else (if n < 36390 then 91 else 294))))) else (if n < 38685 then (if n < 37877 then (if n < 37367 then (if n < 37335 then 115 else (if n < 37365 then 230 else 22)) else (if n < 37845 then 320 else (if n < 37847 then 256 else 159))) else (if n < 38175 then (if n < 37879 then 37 else (if n < 38173 then 27 else 13)) else (if n < 38205 then 87 else (if n < 38207 then 228 else 137)))) else (if n < 40305 then (if n < 38719 then (if n < 38687 then 18 else (if n < 38717 then 179 else 181)) else (if n < 40273 then 104 else (if n < 40275 then 54 else 100))) else (if n < 40787 then (if n < 40307 then 73 else (if n < 40785 then 44 else 260)) else (if n < 40817 then 322 else (if n < 40819 then 336 else 200)))))) else (if n < 45525 then (if n < 42688 then (if n < 41580 then (if n < 41070 then (if n < 41038 then 8 else (if n < 41068 then 371 else 193)) else (if n < 41548 then 114 else (if n < 41550 then 356 else 123))) else (if n < 42178 then (if n < 41582 then 128 else (if n < 42176 then 70 else 133)) else (if n < 42208 then 198 else (if n < 42210 then 218 else 281)))) else (if n < 44068 then (if n < 42722 then (if n < 42690 then 212 else (if n < 42720 then 301 else 30)) else (if n < 44036 then 17 else (if n < 44038 then 35 else 65))) else (if n < 44550 then (if n < 44070 then 60 else (if n < 44548 then 311 else 353)) else (if n < 44580 then 287 else (if n < 44582 then 303 else 3))))) else (if n < 46877 then (if n < 46069 then (if n < 45559 then (if n < 45527 then 253 else (if n < 45557 then 174 else 192)) else (if n < 46037 then 239 else (if n < 46039 then 163 else 375))) else (if n < 46367 then (if n < 46071 then 235 else (if n < 46365 then 189 else 247)) else (if n < 46397 then 329 else (if n < 46399 then 143 else 374)))) else (if n < 48497 then (if n < 46911 then (if n < 46879 then 169 else (if n < 46909 then 244 else 110)) else (if n < 48465 then 154 else (if n < 48467 then 279 else 327))) else (if n < 48979 then (if n < 48499 then 325 else (if n < 48977 then 242 else 382)) else (if n < 49009 then 269 else (if n < 49011 then 263 else 149))))))) else (if n < 57476 then (if n < 53593 then (if n < 50696 then (if n < 49828 then (if n < 49318 then (if n < 49286 then 6 else (if n < 49316 then 9 else 166)) else (if n < 49796 then 94 else (if n < 49798 then 136 else 102))) else (if n < 50186 then (if n < 49830 then 77 else (if n < 50184 then 58 else 29)) else (if n < 50216 then 53 else (if n < 50218 then 48 else 240)))) else (if n < 51296 then (if n < 50730 then (if n < 50698 then 39 else (if n < 50728 then 72 else 274)) else (if n < 51264 then 2 else (if n < 51266 then 0 else 170))) else (if n < 51778 then (if n < 51298 then 144 else (if n < 51776 then 236 else 182)) else (if n < 51808 then 19 else (if n < 51810 then 24 else 14))))) else (if n < 55185 then (if n < 54137 then (if n < 53627 then (if n < 53595 then 293 else (if n < 53625 then 224 else 251)) else (if n < 54105 then 302 else (if n < 54107 then 376 else 286))) else (if n < 54675 then (if n < 54139 then 333 else (if n < 54673 then 361 else 315)) else (if n < 54705 then 248 else (if n < 54707 then 377 else 298)))) else (if n < 55605 then (if n < 55219 then (if n < 55187 then 254 else (if n < 55217 then 317 else 306)) else (if n < 55573 then 363 else (if n < 55575 then 291 else 366))) else (if n < 56087 then (if n < 55607 then 369 else (if n < 56085 then 383 else 358)) else (if n < 56117 then 331 else (if n < 56119 then 335 else 373)))))) else (if n < 61785 then (if n < 58888 then (if n < 58020 then (if n < 57510 then (if n < 57478 then 288 else (if n < 57508 then 207 else 362)) else (if n < 57988 then 147 else (if n < 57990 then 368 else 124))) else (if n < 58378 then (if n < 58022 then 332 else (if n < 58376 then 84 else 381)) else (if n < 58408 then 221 else (if n < 58410 then 204 else 283)))) else (if n < 59488 then (if n < 58922 then (if n < 58890 then 249 else (if n < 58920 then 300 else 305)) else (if n < 59456 then 199 else (if n < 59458 then 155 else 210))) else (if n < 59970 then (if n < 59490 then 195 else (if n < 59968 then 130 else 213)) else (if n < 60000 then 151 else (if n < 60002 then 117 else 357))))) else (if n < 63377 then (if n < 62329 then (if n < 61819 then (if n < 61787 then 95 else (if n < 61817 then 310 else 160)) else (if n < 62297 then 59 else (if n < 62299 then 282 else 348))) else (if n < 62867 then (if n < 62331 then 206 else (if n < 62865 then 34 else 68)) else (if n < 62897 then 112 else (if n < 62899 then 296 else 225)))) else (if n < 63797 then (if n < 63411 then (if n < 63379 then 324 else (if n < 63409 then 63 else 349)) else (if n < 63765 then 40 else (if n < 63767 then 79 else 318))) else (if n < 64279 then (if n < 63799 then 380 else (if n < 64277 then 365 else 119)) else (if n < 64309 then 194 else (if n < 64311 then 217 else 129)))))))))

private def decode (p : Equiv.Perm (Fin 16)) : Index :=
  decodeKey ((p 0).val + 16 * (p 4).val + 256 * (p 8).val + 4096 * (p 12).val)

set_option maxHeartbeats 800000 in
private theorem decode_spec : ∀ i, decode (perm i) = i := by decide +kernel

theorem perm_injective : Function.Injective perm := Function.LeftInverse.injective decode_spec

theorem perm_one : perm 0 = 1 := by decide +kernel

set_option maxHeartbeats 800000 in
theorem next_spec : ∀ i j, perm (next i j) =
    perm i * (![firstA, firstB, firstA⁻¹, firstB⁻¹] : Fin 4 → Equiv.Perm (Fin 16)) j := by
  decide +kernel

set_option maxHeartbeats 800000 in
theorem parent_lt : ∀ i : Index, i ≠ 0 → (parent i).val < i.val := by decide +kernel

set_option maxHeartbeats 800000 in
theorem parent_spec : ∀ i : Index, i ≠ 0 → next (parent i) (lastGen i) = i := by decide +kernel

set_option maxHeartbeats 800000 in
theorem square_spec : ∀ i, perm (square i) = perm i ^ 2 := by decide +kernel

theorem mark_spec : perm markIndex = mark.val := by decide +kernel

private theorem generator_mem (j : Fin 4) :
    (![firstA, firstB, firstA⁻¹, firstB⁻¹] : Fin 4 → Equiv.Perm (Fin 16)) j ∈ firstSubgroup := by
  have hA : firstA ∈ firstSubgroup := Subgroup.subset_closure (by simp)
  have hB : firstB ∈ firstSubgroup := Subgroup.subset_closure (by simp)
  fin_cases j
  · exact hA
  · exact hB
  · exact firstSubgroup.inv_mem hA
  · exact firstSubgroup.inv_mem hB

theorem perm_mem (i : Index) : perm i ∈ firstSubgroup := by
  have h : ∀ n, ∀ i : Index, i.val = n → perm i ∈ firstSubgroup := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      by_cases hz : i = 0
      · rw [hz, perm_one]
        exact firstSubgroup.one_mem
      · rw [← parent_spec i hz, next_spec]
        exact firstSubgroup.mul_mem
          (ih (parent i).val (hi ▸ parent_lt i hz) (parent i) rfl) (generator_mem _)
  exact h i.val i rfl

def element (i : Index) : First := ⟨perm i, perm_mem i⟩

theorem element_injective : Function.Injective element := by
  intro i j h
  exact perm_injective (congrArg Subtype.val h)

theorem element_surjective : Function.Surjective element := by
  intro p
  have h : ∀ q ∈ firstSubgroup, ∃ i, perm i = q := by
    intro q hq
    induction hq using Subgroup.closure_induction_right with
    | one => exact ⟨0, perm_one⟩
    | mul_right q hq r hr ih =>
      obtain ⟨i, rfl⟩ := ih
      rcases hr with rfl | rfl
      · exact ⟨next i 0, next_spec i 0⟩
      · exact ⟨next i 1, next_spec i 1⟩
    | mul_inv_cancel q hq r hr ih =>
      obtain ⟨i, rfl⟩ := ih
      rcases hr with rfl | rfl
      · exact ⟨next i 2, next_spec i 2⟩
      · exact ⟨next i 3, next_spec i 3⟩
  obtain ⟨i, hi⟩ := h p.val p.property
  exact ⟨i, Subtype.ext hi⟩

noncomputable def enumeration : Index ≃ First :=
  Equiv.ofBijective element ⟨element_injective, element_surjective⟩

theorem element_zero : element 0 = 1 := Subtype.ext perm_one

theorem element_mark : element markIndex = mark := Subtype.ext mark_spec

theorem element_square (i : Index) : element (square i) = element i ^ 2 :=
  Subtype.ext (square_spec i)

end Theory.GroupTheory.HeldM22A10.FirstExclusion.FiniteModel
