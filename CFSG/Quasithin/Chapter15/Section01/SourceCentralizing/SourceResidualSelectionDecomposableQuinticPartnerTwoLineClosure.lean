module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreAlternatives

/-!
# The original support images have the original normal closure

The original Sylow subgroup exchanges the two literal supports. Their
images under any action of Mc are therefore conjugate, and their join is
the original V-image. Consequently either support image normally generates
exactly the normal closure of the original V-image. This preserves the
normal subgroup when the transvection classification is applied to one
support actor on the canonical section.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem support_images_conjugate {H : Type*} [Group H]
    (M V₁ V₂ : Subgroup G) (q : M →* H) (t : M)
    (hex : V₁.map (MulAut.conj (t : G)).toMonoidHom = V₂) :
    ((V₁.subgroupOf M).map q).map (MulAut.conj (q t)).toMonoidHom =
      (V₂.subgroupOf M).map q := by
  apply le_antisymm
  · rintro x ⟨y,⟨m,hm,rfl⟩,rfl⟩
    refine ⟨t * m * t⁻¹,?_,?_⟩
    · change (t : G) * (m : G) * (t : G)⁻¹ ∈ V₂
      rw [←hex]
      exact ⟨m,hm,rfl⟩
    · change q (t * m * t⁻¹) = q t * q m * (q t)⁻¹
      simp only [map_mul,map_inv]
  · rintro x ⟨m,hm,rfl⟩
    have hm' : (m : G) ∈ V₁.map (MulAut.conj (t : G)).toMonoidHom := hex ▸ hm
    obtain ⟨v,hv,hvm⟩ := hm'
    let vM : M := t⁻¹ * m * t
    have hvM : (vM : G) = v := by
      change (t : G)⁻¹ * (m : G) * (t : G) = v
      change (t : G) * v * (t : G)⁻¹ = (m : G) at hvm
      rw [←hvm]
      group
    refine ⟨q vM,⟨vM,?_,rfl⟩,?_⟩
    · change (vM : G) ∈ V₁
      rwa [hvM]
    · change q t * q vM * (q t)⁻¹ = q m
      simp only [vM,map_mul,map_inv]
      group


private theorem normalClosure_exchanged_pair {H : Type*} [Group H]
    (A B : Subgroup H) (t : H)
    (hex : A.map (MulAut.conj t).toMonoidHom = B) :
    normalClosure (A : Set H) = normalClosure ((A ⊔ B : Subgroup H) : Set H) := by
  let N := normalClosure (A : Set H)
  have hBN : B ≤ N := by
    rw [←hex]
    rintro x ⟨y,hy,rfl⟩
    exact (inferInstance : N.Normal).conj_mem y (le_normalClosure hy) t
  exact le_antisymm (normalClosure_mono (show A ≤ A ⊔ B from le_sup_left))
    (normalClosure_le_normal (sup_le le_normalClosure hBN))

/-- Each literal support image has the same normal closure as the original
V-image, in any specified action of the actual partner Mc. -/
theorem PreparedChosenModule.decomposable_five_support_image_normalClosure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
        (ρ : Representation (ZMod 2) Mc W) (i : d.Index),
        normalClosure (actionSubgroup ρ
          ((plane V (c.ambientFactor d i).space).subgroupOf Mc) : Set (actionImage ρ)) =
        normalClosure (actionSubgroup ρ (V.subgroupOf Mc) : Set (actionImage ρ)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive W _ _ ρ i
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  obtain ⟨hCMc,_,_,_,_,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let S₀ := (T : Subgroup G) ⊓ normalizer (V₁ : Set G)
  have hSne : S₀ ≠ (T : Subgroup G) := by
    intro he
    have hh : S₀.relIndex (T : Subgroup G) = 2 := s.stabilizer_index
    rw [he,relIndex_self] at hh
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt
    (lt_of_le_of_ne (show S₀ ≤ (T : Subgroup G) from inf_le_left) hSne)
  obtain ⟨hex₁,hex₂⟩ := s.exchanges t ht (fun hh => htS ⟨ht,hh⟩)
  let q := Representation.BinaryOffender.actionHom ρ
  let tMc : Mc := ⟨t,hTMc ht⟩
  let A₁ := actionSubgroup ρ (V₁.subgroupOf Mc)
  let A₂ := actionSubgroup ρ (V₂.subgroupOf Mc)
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  have hjoin : A₁ ⊔ A₂ = A := by
    change (V₁.subgroupOf Mc).map q ⊔ (V₂.subgroupOf Mc).map q = (V.subgroupOf Mc).map q
    rw [←Subgroup.map_sup,←subgroupOf_sup ((plane_le _).trans hVMc)
      ((plane_le _).trans hVMc),s.complement]
  have hc₁ : A₁.map (MulAut.conj (q tMc)).toMonoidHom = A₂ :=
    support_images_conjugate Mc V₁ V₂ q tMc hex₁
  have hc₂ : A₂.map (MulAut.conj (q tMc)).toMonoidHom = A₁ :=
    support_images_conjugate Mc V₂ V₁ q tMc hex₂
  have hh₁ := normalClosure_exchanged_pair A₁ A₂ (q tMc) hc₁
  have hh₂ := normalClosure_exchanged_pair A₂ A₁ (q tMc) hc₂
  rw [hjoin] at hh₁
  rw [sup_comm,hjoin] at hh₂
  rcases s.covers i with hi | hi
  · simpa only [hi] using hh₁
  · simpa only [hi] using hh₂

end CFSG.Quasithin.Chapter15.Section01
