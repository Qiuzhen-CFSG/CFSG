module
public import Theory.GroupTheory.PGroup.ExtraspecialThreeSmallKernel
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Cubic generators lifted through the original two-kernel

A normal subgroup meeting an extraspecial residual of order 27 in order
nine supplies a stable Frattini line. Coprime complements produce two
Sylow-invariant cubic subgroups generating that residual. Taking the
two-residuals of their literal preimages lifts these to generators of the
original two-residual. Each restricted quotient map has kernel exactly
the intrinsic two-core and quotient of order three.

The normalizing two-kernel permits generation to lift without assuming
that it lies in either generator. Normality of the order-nine kernel is
in the supplied quotient group; no ambient normality of the cubic lifts
is asserted. The application is the surviving order-four chief interval
in Aschbacher–Smith 14.7.20(2), using the reducible Sylow step of 14.7.9
and 14.7.15(2), printed pp.1045,1047,1049.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

private theorem cubic_perfect {C : Type*} [Group C] [Finite C]
    (hc : Nat.card C = 3) : IsPPerfect 2 C := by
  apply (pResidual_eq_top_iff 2 C).mp
  apply top_unique
  intro x _
  exact mem_pResidual_of_orderOf_coprime
    ((show Nat.Coprime 2 3 by decide).of_dvd_right (hc ▸ _root_.orderOf_dvd_natCard x))

/-- Take the two-residual of the literal preimage of a cubic subgroup. -/
theorem exists_cubic_residual_lift
    (q : G →* D) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (S : Subgroup G) (C : Subgroup D) (hc : Nat.card C = 3)
    (hn : S.map q ≤ normalizer (C : Set D)) :
    ∃ A : Subgroup G, A ≤ pResidual 2 G ∧ IsPPerfect 2 A ∧
      S ≤ normalizer (A : Set G) ∧ q.ker ≤ normalizer (A : Set G) ∧
      A.map q = C ∧ (q.comp A.subtype).ker = pCore 2 A ∧
      Nat.card (A ⧸ pCore 2 A) = 3 := by
  let B := C.comap q
  let A := (pResidual 2 B).map B.subtype
  have hBA : normalizer (B : Set G) ≤ normalizer (A : Set G) :=
    normalizer_le_normalizer_characteristic_image B (pResidual 2 B)
  have hS : S ≤ normalizer (B : Set G) :=
    (map_le_iff_le_comap.mp hn).trans (C.le_normalizer_comap q)
  have hkB : q.ker ≤ B := fun x hx => by
    change q x ∈ C
    rw [hx]
    exact C.one_mem
  have him : A.map q = C := by
    rw [map_embedded_pResidual,show B.map q = C from map_comap_eq_self_of_surjective hq C,
      (pResidual_eq_top_iff 2 C).mpr (cubic_perfect hc),←MonoidHom.range_eq_map,range_subtype]
  let f := q.comp A.subtype
  have hf : IsPGroup 2 f.ker := hk.comap_of_injective _ A.subtype_injective
  have hrange : f.range = C := by rw [MonoidHom.range_comp,range_subtype,him]
  have hthree : IsPGroup 3 f.range := by
    rw [hrange]
    exact IsPGroup.of_card (n := 1) (by simpa using hc)
  have hcore : pCore 2 f.range = ⊥ := by
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (hthree.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have he := f.ker_eq_pCore_of_range_core_eq_bot 2 hf hcore
  refine ⟨A,map_pResidual_le 2 B.subtype,isPPerfect_embedded_pResidual 2 B,
    hS.trans hBA,(hkB.trans B.le_normalizer).trans hBA,him,he,?_⟩
  rw [←he,Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hrange,hc]

/-- Cubic image generators lift to generators of the original two-residual. -/
theorem exists_generating_cubic_residual_lifts
    (q : G →* D) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (S : Subgroup G) (C E : Subgroup D) (hc : Nat.card C = 3) (he : Nat.card E = 3)
    (hnC : S.map q ≤ normalizer (C : Set D))
    (hnE : S.map q ≤ normalizer (E : Set D))
    (hgen : C ⊔ E = pResidual 2 D) :
    ∃ A B : Subgroup G, A ⊔ B = pResidual 2 G ∧
      (IsPPerfect 2 A ∧ S ≤ normalizer (A : Set G) ∧ A.map q = C ∧
        (q.comp A.subtype).ker = pCore 2 A ∧ Nat.card (A ⧸ pCore 2 A) = 3) ∧
      (IsPPerfect 2 B ∧ S ≤ normalizer (B : Set G) ∧ B.map q = E ∧
        (q.comp B.subtype).ker = pCore 2 B ∧ Nat.card (B ⧸ pCore 2 B) = 3) := by
  obtain ⟨A,hAR,hA,hSA,hkA,himA,hkerA,hcardA⟩ :=
    exists_cubic_residual_lift q hq hk S C hc hnC
  obtain ⟨B,hBR,hB,hSB,hkB,himB,hkerB,hcardB⟩ :=
    exists_cubic_residual_lift q hq hk S E he hnE
  refine ⟨A,B,le_antisymm (sup_le hAR hBR) ?_,
    ⟨hA,hSA,himA,hkerA,hcardA⟩,⟨hB,hSB,himB,hkerB,hcardB⟩⟩
  apply isPPerfect_le_of_map_le_of_kernel_normalizes q (pResidual 2 G) (A ⊔ B)
    (isPPerfect_pResidual 2) hk
    ((le_inf hkA hkB).trans (normalizer_inf_normalizer_le_normalizer_sup A B))
  rw [Subgroup.map_sup,himA,himB,hgen,map_pResidual_of_surjective 2 q hq]
end Subgroup
namespace IsExtraspecial
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- A stable order-nine subgroup supplies two normalized cubic generators. -/
theorem cubic_generators_of_normal_nine
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (N : Subgroup D) [N.Normal] (hN : Nat.card (N.subgroupOf P) = 9)
    (hZ : center P ≤ N.subgroupOf P) (S : Subgroup D) (hS : IsPGroup 2 S) :
    ∃ C E : Subgroup D, C ≤ P ∧ E ≤ P ∧ Nat.card C = 3 ∧ Nat.card E = 3 ∧
      C ≠ (center P).map P.subtype ∧ E ≠ (center P).map P.subtype ∧
      C ⊔ E = P ∧ S ≤ normalizer (C : Set D) ∧ S ≤ normalizer (E : Set D) := by
  let α : S →* MulAut P := (MulAut.conjNormal : D →* MulAut P).comp S.subtype
  let q := QuotientGroup.mk' (frattini P)
  let J := (N.subgroupOf P).map q
  have hφ : frattini P ≤ N.subgroupOf P := by
    rwa [IsExtraspecial.frattini_eq_center (p := 3)]
  have hpre : J.comap q = N.subgroupOf P := by
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hφ]
  have hJ0 : J ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.comap q) he
    rw [hpre,MonoidHom.comap_bot,QuotientGroup.ker_mk',IsExtraspecial.frattini_eq_center (p := 3)] at hh
    have hc := congrArg (fun A : Subgroup P => Nat.card A) hh
    rw [hN,IsExtraspecial.center_order_p 3 P] at hc
    omega
  have hJ1 : J ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.comap q) he
    rw [hpre,comap_top] at hh
    have hc := congrArg (fun A : Subgroup P => Nat.card A) hh
    rw [hN,card_top,hP] at hc
    omega
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨n,hn⟩ := hS.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  obtain ⟨C,E,hC,hE,hCZ,hEZ,hCE,hCS,hES⟩ :=
    ExtraspecialSylow.exists_normalized_cubic_generators α hcop hP hexp J hJ0 hJ1
      (by
        rintro a _ ⟨x,hx,rfl⟩
        rw [quotientAut_apply_mk]
        exact mem_map_of_mem q ((inferInstance : N.Normal).conj_mem x hx a))
  have hn (B : Subgroup P) (hb : ∀ a : S, ∀ x ∈ B, α a x ∈ B) :
      S ≤ normalizer (B.map P.subtype : Set D) := by
    apply le_normalizer_iff.mpr
    rintro a ha _ ⟨x,hx,rfl⟩
    exact mem_map_of_mem P.subtype (hb ⟨a,ha⟩ x hx)
  refine ⟨C.map P.subtype,E.map P.subtype,map_subtype_le _,map_subtype_le _,
    ?_,?_,?_,?_,?_,hn C hCS,hn E hES⟩
  · rw [card_map_of_injective P.subtype_injective,hC]
  · rw [card_map_of_injective P.subtype_injective,hE]
  · exact fun he => hCZ ((map_injective P.subtype_injective) he)
  · exact fun he => hEZ ((map_injective P.subtype_injective) he)
  · rw [←Subgroup.map_sup,hCE,←MonoidHom.range_eq_map,range_subtype]

/-- The original two-residual is generated by two normalized cubic lifts. -/
theorem exists_cubic_lifts_of_normal_nine
    (q : G →* D) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hP : Nat.card (pResidual 2 D) = 27) [IsExtraspecial 3 (pResidual 2 D)]
    (hexp : Monoid.exponent (pResidual 2 D) = 3)
    (N : Subgroup D) [N.Normal] (hN : Nat.card (N.subgroupOf (pResidual 2 D)) = 9)
    (hZ : center (pResidual 2 D) ≤ N.subgroupOf (pResidual 2 D))
    (S : Subgroup G) (hS : IsPGroup 2 S) :
    ∃ A B : Subgroup G, A ⊔ B = pResidual 2 G ∧
      (IsPPerfect 2 A ∧ S ≤ normalizer (A : Set G) ∧ Nat.card (A.map q) = 3 ∧
        A.map q ≠ (center (pResidual 2 D)).map (pResidual 2 D).subtype ∧
        (q.comp A.subtype).ker = pCore 2 A ∧ Nat.card (A ⧸ pCore 2 A) = 3) ∧
      (IsPPerfect 2 B ∧ S ≤ normalizer (B : Set G) ∧ Nat.card (B.map q) = 3 ∧
        B.map q ≠ (center (pResidual 2 D)).map (pResidual 2 D).subtype ∧
        (q.comp B.subtype).ker = pCore 2 B ∧ Nat.card (B ⧸ pCore 2 B) = 3) := by
  obtain ⟨C,E,_,_,hC,hE,hCZ,hEZ,hCE,hCS,hES⟩ :=
    cubic_generators_of_normal_nine (pResidual 2 D) hP hexp N hN hZ (S.map q) (hS.map q)
  obtain ⟨A,B,hAB,⟨hA,hSA,himA,hkerA,hcardA⟩,⟨hB,hSB,himB,hkerB,hcardB⟩⟩ :=
    exists_generating_cubic_residual_lifts q hq hk S C E hC hE hCS hES hCE
  exact ⟨A,B,hAB,⟨hA,hSA,himA ▸ hC,himA ▸ hCZ,hkerA,hcardA⟩,
    ⟨hB,hSB,himB ▸ hE,himB ▸ hEZ,hkerB,hcardB⟩⟩
end IsExtraspecial
