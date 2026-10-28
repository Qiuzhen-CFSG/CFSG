module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.FiveLocal
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.BaumeisterParabolics
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicProjective
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Eight

/-!
# The literal second parabolic and its cubic quotient

For the cubic selected by the field-affine embedding, L₁₂ has order thirty
and centralizes that cubic. Its image in the centralizer quotient has
order ten. The dihedral-centralizer recognition excludes the order-168
alternative using this actual divisor, identifying the quotient with A₆.
The image of L₁₂ is D₁₀ and is a self-normalizing Sylow-five normalizer.

Frattini's argument in the index-two extension of A₆ gives normalizer
order twenty. Taking the full preimage under the original cubic map proves
|N_G(L₁₂)| = 60 and C_G(s) ∩ N_G(L₁₂) = L₁₂, and supplies an actual
cubic inverter in N_G(L₁₂). This does not yet identify that group with
S₃ × D₁₀ or assert that the inverter has order two.

Source: Baumeister, A geometry for groups of J₃-type (2007), Lemmas 2.4–2.5,
pp.495–496. The original terminal application is in `ParabolicApplication`.
-/

open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G]

/-- The literal field complement has order thirty. -/
theorem overlap_card (j : Model →* G) (hj : Function.Injective j) :
    Nat.card (overlap j) = 30 := by
  rw [Nat.card_congr (overlapEquiv j hj).toEquiv]
  change Nat.card (Multiplicative (ZMod 3) × DihedralGroup 5) = 30
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card, DihedralGroup.nat_card]

/-- Every element of the chosen overlap centralizes its own cubic. -/
theorem overlap_le_cubic_centralizer (j : Model →* G) :
    overlap j ≤ centralizer ({j cubic} : Set G) := by
  rintro _ ⟨x,hx,rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (((cubic_commutes_complement ⟨x,hx⟩).map j).symm.eq)

/-- The same cubic kernel lies in the literal overlap. -/
theorem cubic_le_overlap (j : Model →* G) : zpowers (j cubic) ≤ overlap j :=
  zpowers_le.mpr (mem_map_of_mem j cubic_mem)

private theorem quotient_image_card {H K : Type*} [Group H] [Group K] [Finite H]
    (q : H →* K) (B : Subgroup H) (hk : q.ker ≤ B)
    (hker : Nat.card q.ker = 3) (hB : Nat.card B = 30) :
    Nat.card (B.map q) = 10 := by
  have hh := (q.ker.subgroupOf B).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv, hker, hB] at hh
  change q.ker.relIndex B * 3 = 30 at hh
  rw [relIndex_ker] at hh
  omega

private theorem alternatingSix_of_ten_dihedral {H : Type*} [Group H] [Finite H]
    (h10 : 10 ∣ Nat.card H)
    (h : ∀ t : H, orderOf t = 2 → Nonempty (centralizer ({t} : Set H) ≃* DihedralGroup 4)) :
    Nonempty (H ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := H) 2
    ((by decide : 2 ∣ 10).trans h10)
  let D : DihedralInvolutionCentralizerHypotheses H 3 := {
    two_le := by decide
    z := t
    involution := ⟨by intro h1; simp [h1] at ht, ht ▸ pow_orderOf_eq_one t⟩
    involutions_conjugate := fun u hu => isConj_iff.mp
      (Sporadic.Janko3.SourceRecognition.CentralCubicQuotient.dihedral_centralizers_fusion h u t
        (orderOf_eq_prime hu.2 hu.1) ht)
    centralizer_equiv := h t ht }
  rcases D.recognize_eight with he | he
  · obtain ⟨e⟩ := he
    have hcard : Nat.card H = 168 := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.card_congr Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm.toEquiv).trans
        Atlas.Comparisons.Exceptional.sl3Two_card
    rw [hcard] at h10
    norm_num at h10
  · exact he

private theorem quotient_image_dihedral {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (q : H →* K) (B : Subgroup H) (hk : q.ker ≤ B) (hker : Nat.card q.ker = 3)
    (eB : B ≃* (Multiplicative (ZMod 3) × DihedralGroup 5)) :
    Nonempty (B.map q ≃* DihedralGroup 5) := by
  let i0 : DihedralGroup 5 →* B := eB.symm.toMonoidHom.comp
    (MonoidHom.inr (Multiplicative (ZMod 3)) (DihedralGroup 5))
  let i := B.subtype.comp i0
  have hi : Function.Injective i := B.subtype_injective.comp
    (eB.symm.injective.comp (fun _ _ hh => congrArg Prod.snd hh))
  let f := q.comp i
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hxk : i x ∈ q.ker := hx
    have h3 : orderOf x ∣ 3 := by
      have hh := q.ker.orderOf_dvd_natCard hxk
      rwa [orderOf_injective i hi,hker] at hh
    have h10 : orderOf x ∣ 10 := by simpa only [DihedralGroup.nat_card] using orderOf_dvd_natCard x
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (Nat.dvd_gcd h3 h10))
  let d := f.codRestrict (B.map q) (fun x => mem_map_of_mem q (i0 x).property)
  have hd : Function.Injective d := fun x y hh => hf (congrArg Subtype.val hh)
  have hB : Nat.card B = 30 := by
    rw [Nat.card_congr eB.toEquiv,Nat.card_prod,Nat.card_eq_fintype_card,
      Fintype.card_multiplicative,ZMod.card,DihedralGroup.nat_card]
  have he : Nat.card (DihedralGroup 5) = Nat.card (B.map q) := by
    rw [DihedralGroup.nat_card,quotient_image_card q B hk hker hB]
  exact ⟨(MulEquiv.ofBijective d ((Nat.bijective_iff_injective_and_card d).mpr ⟨hd,he⟩)).symm⟩

variable [Finite G]

private theorem ten_normalizer_in_extension
    (L : Subgroup G) [L.Normal] (e : L ≃* alternatingGroup (Fin 6))
    (hL : L.index = 2) (B : Subgroup G) (hBL : B ≤ L) (hB : Nat.card B = 10) :
    Nat.card (normalizer (B : Set G)) = 20 := by
  let B0 := B.subgroupOf L
  let B6 := B0.map e.toMonoidHom
  have hB0 : Nat.card B0 = 10 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv).trans hB
  have hB6 : Nat.card B6 = 10 := (card_map_of_injective e.injective).trans hB0
  obtain ⟨P,hP⟩ := ten_eq_five_normalizer B6 hB6
  change normalizer (((P : Subgroup (alternatingGroup (Fin 6))) : Set (alternatingGroup (Fin 6)))) = B6 at hP
  let Q : Sylow 5 L := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQ : normalizer ((Q : Subgroup L) : Set L) = B0 := by
    change normalizer (((P : Subgroup (alternatingGroup (Fin 6))).map
      e.symm.toMonoidHom) : Set L) = B0
    rw [← map_equiv_normalizer_eq,hP]
    ext x
    simp only [B6,mem_map_equiv,MulEquiv.symm_symm,e.symm_apply_apply]
  let R := (Q : Subgroup L).map L.subtype
  have hR : R.subgroupOf L = (Q : Subgroup L) := by
    change ((Q : Subgroup L).map L.subtype).comap L.subtype = _
    rw [comap_map_eq,L.ker_subtype,sup_bot_eq]
  have hBnormal : normalizer (B0 : Set L) = B0 := by
    rw [← hQ]
    exact Q.normalizer_normalizer
  have hinf : normalizer (B : Set G) ⊓ L = B := by
    rw [← subgroupOf_map_subtype,subgroupOf_normalizer_eq hBL,hBnormal,
      map_subgroupOf_eq_of_le hBL]
  have hRB : normalizer (R : Set G) ⊓ L = B := by
    rw [← subgroupOf_map_subtype,subgroupOf_normalizer_eq (map_subtype_le _),hR,hQ,
      map_subgroupOf_eq_of_le hBL]
  have hn : normalizer (R : Set G) ≤ normalizer (B : Set G) := by
    rw [← hRB]
    exact (le_inf (normalizer (R : Set G)).le_normalizer
      (le_normalizer_of_normal : normalizer (R : Set G) ≤ normalizer (L : Set G))).trans
        inf_normalizer_le_normalizer_inf
  have hsup : normalizer (B : Set G) ⊔ L = ⊤ := by
    apply top_unique
    rw [← Q.normalizer_sup_eq_top]
    exact sup_le_sup_right hn L
  have hLc : Nat.card L = 360 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hGc : Nat.card G = 720 := by
    have hh := L.card_mul_index
    rw [hLc,hL] at hh
    omega
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    L (normalizer (B : Set G))
    (le_normalizer_of_normal : normalizer (B : Set G) ≤ normalizer (L : Set G))
  rw [hLc,inf_comm L,hinf,hB,sup_comm L,hsup,card_top,hGc] at hh
  omega

/-- Recognize the centralizer quotient of the cubic from this field embedding. -/
theorem field_cubic_quotient {z : G} (h : HTypeAt z) (hc : OneInvolutionClass G)
    (j : Model →* G) (hj : Function.Injective j) :
    Nonempty ((centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic)) ≃*
      alternatingGroup (Fin 6)) := by
  let C := centralizer ({j cubic} : Set G)
  let q := QuotientGroup.mk' (cubicKernel (j cubic))
  let B := (overlap j).subgroupOf C
  have hs : orderOf (j cubic) = 3 := (orderOf_injective j hj cubic).trans cubic_order
  have hk : q.ker ≤ B := by
    rw [QuotientGroup.ker_mk']
    exact fun _ hx => cubic_le_overlap j hx
  have hB : Nat.card B = 30 :=
    (Nat.card_congr (subgroupOfEquivOfLe (overlap_le_cubic_centralizer j)).toEquiv).trans
      (overlap_card j hj)
  have hq : Nat.card (B.map q) = 10 := quotient_image_card q B hk
    (by rw [QuotientGroup.ker_mk',cubicKernel_card _ hs]) hB
  apply alternatingSix_of_ten_dihedral
    (hq ▸ (B.map q).card_subgroup_dvd_card)
  exact cubic_quotient_involution_centralizers h hc _ hs

/-- The actual quotient image is a Sylow-five normalizer, with its full preimage retained. -/
theorem field_overlap_quotient_image
    (j : Model →* G) (hj : Function.Injective j)
    (e : (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic)) ≃*
      alternatingGroup (Fin 6)) :
    let C := centralizer ({j cubic} : Set G)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (cubicKernel (j cubic)))
    let B := (overlap j).subgroupOf C
    ∃ P : Sylow 5 (alternatingGroup (Fin 6)),
      B.map q = normalizer (P : Set (alternatingGroup (Fin 6))) ∧
      (normalizer (P : Set (alternatingGroup (Fin 6)))).comap q = B ∧
      normalizer (B : Set C) = B := by
  dsimp only
  let C := centralizer ({j cubic} : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (cubicKernel (j cubic)))
  let B := (overlap j).subgroupOf C
  have hker : q.ker = cubicKernel (j cubic) := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hk : q.ker ≤ B := by rw [hker]; exact fun _ hx => cubic_le_overlap j hx
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hB : Nat.card B = 30 :=
    (Nat.card_congr (subgroupOfEquivOfLe (overlap_le_cubic_centralizer j)).toEquiv).trans
      (overlap_card j hj)
  have him : Nat.card (B.map q) = 10 := quotient_image_card q B hk (by
    rw [hker,cubicKernel_card _ ((orderOf_injective j hj cubic).trans cubic_order)]) hB
  have hpre : (B.map q).comap q = B := by rw [comap_map_eq,sup_eq_left.mpr hk]
  obtain ⟨P,hP⟩ := ten_eq_five_normalizer (B.map q) him
  refine ⟨P,hP.symm,hP.symm ▸ hpre,?_⟩
  calc
    normalizer (B : Set C) = normalizer (((B.map q).comap q : Subgroup C) : Set C) := by rw [hpre]
    _ = (normalizer (B.map q : Set (alternatingGroup (Fin 6)))).comap q :=
      (comap_normalizer_eq_of_surjective _ hq).symm
    _ = B := by rw [ten_self_normalizing _ him,hpre]

/-- The actual overlap image is dihedral of order ten. -/
theorem field_overlap_quotient_dihedral
    (j : Model →* G) (hj : Function.Injective j)
    (e : (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic)) ≃*
      alternatingGroup (Fin 6)) :
    let C := centralizer ({j cubic} : Set G)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (cubicKernel (j cubic)))
    Nonempty (((overlap j).subgroupOf C).map q ≃* DihedralGroup 5) := by
  dsimp only
  let C := centralizer ({j cubic} : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (cubicKernel (j cubic)))
  have hker : q.ker = cubicKernel (j cubic) := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  apply quotient_image_dihedral q ((overlap j).subgroupOf C)
  · rw [hker]
    exact fun _ hx => cubic_le_overlap j hx
  · rw [hker,cubicKernel_card _ ((orderOf_injective j hj cubic).trans cubic_order)]
  · exact (subgroupOfEquivOfLe (overlap_le_cubic_centralizer j)).trans (overlapEquiv j hj)

/-- The centralizer intersection in the literal second parabolic. -/
theorem field_overlap_centralizer_intersection
    (j : Model →* G) (hj : Function.Injective j)
    (e : (centralizer ({j cubic} : Set G) ⧸ cubicKernel (j cubic)) ≃*
      alternatingGroup (Fin 6)) :
    centralizer ({j cubic} : Set G) ⊓ Seventeen.second (overlap j) = overlap j := by
  obtain ⟨P,hP,hpre,hn⟩ := field_overlap_quotient_image j hj e
  apply le_antisymm
  · rintro x ⟨hx,hxn⟩
    have hh : (⟨x,hx⟩ : centralizer ({j cubic} : Set G)) ∈
        (normalizer (overlap j : Set G)).subgroupOf (centralizer ({j cubic} : Set G)) := hxn
    rw [subgroupOf_normalizer_eq (overlap_le_cubic_centralizer j),hn] at hh
    exact hh
  · exact le_inf (overlap_le_cubic_centralizer j) (overlap j).le_normalizer

omit [Finite G] in
/-- The normalizer of the quotient image pulls back to the literal second parabolic. -/
theorem field_pair_quotient_preimage
    (j : Model →* G) (hj : Function.Injective j) :
    let N := normalizer (zpowers (j cubic) : Set G)
    let q := QuotientGroup.mk' (cubicNormalizerKernel (j cubic))
    let B := (overlap j).subgroupOf N
    (normalizer (B.map q : Set (N ⧸ cubicNormalizerKernel (j cubic)))).comap q =
      (Seventeen.second (overlap j)).subgroupOf N := by
  dsimp only
  let N := normalizer (zpowers (j cubic) : Set G)
  let q := QuotientGroup.mk' (cubicNormalizerKernel (j cubic))
  let B := (overlap j).subgroupOf N
  have hk : q.ker ≤ B := by
    rw [QuotientGroup.ker_mk']
    exact fun _ hx => cubic_le_overlap j hx
  have hpre : (B.map q).comap q = B := by rw [comap_map_eq,sup_eq_left.mpr hk]
  rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),hpre]
  exact (subgroupOf_normalizer_eq
    ((overlap j).le_normalizer.trans (overlap_normalizer_le_cubic j hj))).symm

/-- The actual second parabolic has order sixty. -/
theorem field_pair_card {z : G} (h : HTypeAt z) (hc : OneInvolutionClass G)
    (j : Model →* G) (hj : Function.Injective j) :
    Nat.card (Seventeen.second (overlap j)) = 60 := by
  obtain ⟨e⟩ := field_cubic_quotient h hc j hj
  let s := j cubic
  have hs : orderOf s = 3 := (orderOf_injective j hj cubic).trans cubic_order
  let N := normalizer (zpowers s : Set G)
  let q := QuotientGroup.mk' (cubicNormalizerKernel s)
  let B := (overlap j).subgroupOf N
  let L := (cubicQuotientInclusion s).range
  have hL : L.index = 2 := cubicQuotientInclusion_index h hc s hs e
  let : L.Normal := normal_of_index_eq_two hL
  let eL : L ≃* alternatingGroup (Fin 6) :=
    (MonoidHom.ofInjective (cubicQuotientInclusion_injective s)).symm.trans e
  have hB : Nat.card B = 30 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      ((overlap j).le_normalizer.trans (overlap_normalizer_le_cubic j hj))).toEquiv).trans
      (overlap_card j hj)
  have hk : q.ker ≤ B := by rw [QuotientGroup.ker_mk']; exact fun _ hx => cubic_le_overlap j hx
  have hkcard : Nat.card q.ker = 3 := by
    rw [QuotientGroup.ker_mk',cubicNormalizerKernel_card s hs]
  have him : Nat.card (B.map q) = 10 := quotient_image_card q B hk hkcard hB
  have hBL : B.map q ≤ L := by
    rintro _ ⟨b,hb,rfl⟩
    exact (cubicQuotientInclusion_preimage s b).mpr (overlap_le_cubic_centralizer j hb)
  have hn : Nat.card (normalizer (B.map q : Set (N ⧸ cubicNormalizerKernel s))) = 20 :=
    ten_normalizer_in_extension L eL hL (B.map q) hBL him
  let H := (Seventeen.second (overlap j)).subgroupOf N
  have heq : (normalizer (B.map q : Set (N ⧸ cubicNormalizerKernel s))).comap q = H :=
    field_pair_quotient_preimage j hj
  have hmap : H.map q = normalizer (B.map q : Set (N ⧸ cubicNormalizerKernel s)) := by
    rw [← heq,map_comap_eq_self]
    rw [q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective _)]
    exact le_top
  have hkH : q.ker ≤ H := hk.trans (fun _ hb => (overlap j).le_normalizer hb)
  have hcard := (q.ker.subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hkH).toEquiv,hkcard] at hcard
  change q.ker.relIndex H * 3 = Nat.card H at hcard
  rw [relIndex_ker,hmap,hn] at hcard
  have hH : Nat.card H = Nat.card (Seventeen.second (overlap j)) :=
    Nat.card_congr (subgroupOfEquivOfLe (overlap_normalizer_le_cubic j hj)).toEquiv
  omega

/-- The second parabolic contains an inverter of the same cubic; no involution claim is assumed. -/
theorem field_pair_inverter {z : G} (h : HTypeAt z) (hc : OneInvolutionClass G)
    (j : Model →* G) (hj : Function.Injective j) :
    ∃ r ∈ Seventeen.second (overlap j), r * j cubic * r⁻¹ = (j cubic)⁻¹ := by
  classical
  obtain ⟨e⟩ := field_cubic_quotient h hc j hj
  have hmeet := field_overlap_centralizer_intersection j hj e
  have hn : ¬ Seventeen.second (overlap j) ≤ centralizer ({j cubic} : Set G) := by
    intro hh
    have hle : Seventeen.second (overlap j) ≤ overlap j := fun x hx =>
      hmeet ▸ (show x ∈ centralizer ({j cubic} : Set G) ⊓ Seventeen.second (overlap j)
        from ⟨hh hx,hx⟩)
    have hcard := card_le_of_le hle
    rw [field_pair_card h hc j hj,overlap_card j hj] at hcard
    omega
  obtain ⟨r,hr,hrC⟩ := SetLike.not_le_iff_exists.mp hn
  have hs : orderOf (j cubic) = 3 := (orderOf_injective j hj cubic).trans cubic_order
  have hmem : r * j cubic * r⁻¹ ∈ zpowers (j cubic) :=
    (mem_normalizer_iff.mp (overlap_normalizer_le_cubic j hj hr) _).mp (mem_zpowers _)
  rw [mem_zpowers_iff_mem_range_orderOf,hs] at hmem
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hmem
  have hn3 : n < 3 := Finset.mem_range.mp hn
  refine ⟨r,hr,?_⟩
  interval_cases n
  · have hu : r * j cubic * r⁻¹ = 1 := by simpa using he.symm
    have hs1 : j cubic = 1 := (MulAut.conj r).injective (hu.trans (map_one _).symm)
    simp [hs1] at hs
  · have hu : r * j cubic * r⁻¹ = j cubic := by simpa using he.symm
    exact (hrC (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hu))).elim
  · have hu : j cubic ^ 2 = (j cubic)⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ]
      simpa only [hs] using pow_orderOf_eq_one (j cubic))
    exact he.symm.trans hu

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
