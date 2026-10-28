module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceSetup
public import Theory.SpecificGroups.AlternatingSix.AlternatingFourNaturalFixer
public import Theory.GroupTheory.ElementaryDihedralIndexTwo
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSylow
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.FactorPair

/-!
# The cyclic component centralizer in the paired-cubic source

The natural A₆ action makes C_R(K) have index two in C_R(L), where the
original first block L is A₄. If the original involution is unique in
C_R(K), the elementary-factor times D₈ coordinates force that factor to
vanish and identify C_R(K) with C₄. The full automorphism image and the
original Sylow index show this is Sylow in C_G₂(K); the odd-core conclusion
and the cyclic Sylow complement theorem identify the entire centralizer.

The literal terminal consumer below applies the existing component-Sylow,
right-conjugate factor, and pure-fusion theorems. It retains the substantial
earlier source36 unique-involution input and the independently constructed
source30 product coordinates and source37 six-point fusion bound.

Source: Aschbacher–Smith 2.4.36, printed pp.549–550, combined manuscript
of 1 March 2004.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.DoubleA3
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
theorem SourceComponentGeometry.centralizer_index_two
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (L : Subgroup (involutionCentralizer c.z)) (hLK : L ≤ c.K)
    (eL : L ≃* alternatingGroup (Fin 4))
    (huR : c.u ∈ (sourceR d).subgroupOf (involutionCentralizer c.z))
    (huL : c.u ∈ centralizer (L : Set (involutionCentralizer c.z))) :
    (((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (c.K : Set (involutionCentralizer c.z))).subgroupOf
      ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
        centralizer (L : Set (involutionCentralizer c.z)))).index = 2 := by
  let H := involutionCentralizer c.z
  let R := (sourceR d).subgroupOf H
  let C := R ⊓ centralizer (L : Set H)
  let A := conjugationAction c.K c.componentEquiv
  let F := (L.subgroupOf c.K).map c.componentEquiv.toMonoidHom
  let eF : F ≃* alternatingGroup (Fin 4) :=
    ((L.subgroupOf c.K).equivMapOfInjective c.componentEquiv.toMonoidHom
      c.componentEquiv.injective).symm.trans ((subgroupOfEquivOfLe hLK).trans eL)
  let N := C.map A
  have hN : N ≤ natural := (map_mono (show C ≤ R from inf_le_left)).trans c.natural_thompson
  have hfix : ∀ a ∈ N, ∀ l ∈ F, a l = l := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨k, hk, rfl⟩
    change (conjugationAction c.K c.componentEquiv r) (c.componentEquiv k) = c.componentEquiv k
    rw [conjugationAction_apply]
    apply congrArg c.componentEquiv
    apply Subtype.ext
    change r * (k : H) * r⁻¹ = k
    exact mul_inv_eq_iff_eq_mul.mpr (hr.2 k hk).symm
  have hNle : Nat.card N ≤ 2 :=
    AlternatingSix.alternatingFour_natural_fixer_card_le_two F eF N hN hfix
  have hNu : A c.u ∈ N := mem_map_of_mem A ⟨huR, huL⟩
  have huA : A c.u ≠ 1 := by
    change conjugationAction c.K c.componentEquiv c.u ≠ 1
    rw [c.transposition]
    intro h
    have hσ : c.σ = 1 := permutationAction_injective (h.trans (map_one permutationAction).symm)
    have hs := c.swap.sign_eq
    rw [hσ] at hs
    norm_num at hs
  have hNbot : N ≠ ⊥ := by
    intro h
    exact huA (by simpa only [h, mem_bot] using hNu)
  have hNcard : Nat.card N = 2 := by
    have hNpos := (N.one_lt_card_iff_ne_bot).mpr hNbot
    omega
  let f : C →* AutA6 := A.comp C.subtype
  have hrange : f.range = N := by
    rw [MonoidHom.range_comp, C.range_subtype]
  have hker : f.ker = (R ⊓ centralizer (c.K : Set H)).subgroupOf C := by
    ext a
    change A a = 1 ↔ a.val ∈ R ⊓ centralizer (c.K : Set H)
    rw [← MonoidHom.mem_ker, conjugationAction_ker]
    exact ⟨fun h => ⟨a.property.1, h⟩, fun h => h.2⟩
  change ((R ⊓ centralizer (c.K : Set H)).subgroupOf C).index = 2
  rw [← hker, index_ker, hrange, hNcard]

/-- The actual C_R(L) coordinates and unique-involution claim give the
cyclic-four component centralizer inside R. -/
theorem SourceComponentGeometry.centralizer_cyclic_four_of_unique
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (L : Subgroup (involutionCentralizer c.z)) (hLK : L ≤ c.K)
    (eL : L ≃* alternatingGroup (Fin 4))
    (huR : c.u ∈ (sourceR d).subgroupOf (involutionCentralizer c.z))
    (huL : c.u ∈ centralizer (L : Set (involutionCentralizer c.z)))
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (eC : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (L : Set (involutionCentralizer c.z)) : Subgroup (involutionCentralizer c.z)) ≃* (E × DihedralGroup 4))
    (hu : ∃! z : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (c.K : Set (involutionCentralizer c.z)) : Subgroup (involutionCentralizer c.z)), orderOf z = 2) :
    Nat.card E = 1 ∧ Nonempty (((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (c.K : Set (involutionCentralizer c.z)) : Subgroup (involutionCentralizer c.z)) ≃* Multiplicative (ZMod 4)) := by
  let R := (sourceR d).subgroupOf (involutionCentralizer c.z)
  let C := R ⊓ centralizer (L : Set (involutionCentralizer c.z))
  let B := R ⊓ centralizer (c.K : Set (involutionCentralizer c.z))
  have hBC : B ≤ C := inf_le_inf_left R (centralizer_le hLK)
  let eB : B.subgroupOf C ≃* B := subgroupOfEquivOfLe hBC
  have huB : ∃! z : B.subgroupOf C, orderOf z = 2 := by
    obtain ⟨z, hz, huniq⟩ := hu
    refine ⟨eB.symm z, (eB.symm.orderOf_eq z).trans hz, ?_⟩
    intro a ha
    apply eB.injective
    rw [eB.apply_symm_apply]
    exact huniq _ ((eB.orderOf_eq a).trans ha)
  obtain ⟨hE, ⟨e⟩⟩ := Theory.GroupTheory.cyclic_four_of_unique_involution_index_two eC
    (B.subgroupOf C) (c.centralizer_index_two L hLK eL huR huL) huB
  exact ⟨hE, ⟨eB.symm.trans e⟩⟩

/-- The cyclic-four centralizer inside R is the full component centralizer.
The odd-core hypothesis is the earlier source conclusion preceding 2.4.32. -/
theorem SourceComponentGeometry.full_centralizer_of_cyclic_four
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (hi : (((sourceR d).subgroupOf (involutionCentralizer c.z)).subgroupOf
      (c.S₁ : Subgroup (involutionCentralizer c.z))).index = 2)
    (hR : Nat.card (sourceR d) = 64)
    (hodd : pPrimeCore 2 (involutionCentralizer c.z) = ⊥)
    (eB : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (c.K : Set (involutionCentralizer c.z)) : Subgroup (involutionCentralizer c.z)) ≃*
        Multiplicative (ZMod 4)) :
    centralizer (c.K : Set (involutionCentralizer c.z)) ≤
      (sourceR d).subgroupOf (involutionCentralizer c.z) ∧
    Nonempty (centralizer (c.K : Set (involutionCentralizer c.z)) ≃*
      Multiplicative (ZMod 4)) := by
  let H := involutionCentralizer c.z
  let R := (sourceR d).subgroupOf H
  let S : Subgroup H := c.S₁
  let C := centralizer (c.K : Set H)
  let B := R ⊓ C
  let A := conjugationAction c.K c.componentEquiv
  have hs : Function.Surjective A := conjugation_surjective_of_source_outer_actions
    c.K c.componentEquiv c.u c.x c.σ c.swap c.transposition c.outside_natural
  let Q := c.S₁.mapSurjective hs
  let f : S →* AutA6 := A.comp S.subtype
  have hf : f.range = (Q : Subgroup AutA6) := by
    rw [MonoidHom.range_comp, S.range_subtype]
    rfl
  have hk : f.ker = C.subgroupOf S := by
    change A.ker.comap S.subtype = C.subgroupOf S
    rw [conjugationAction_ker]
    rfl
  have hcR : Nat.card R = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe c.thompson_le).toEquiv).trans hR
  have hcS : Nat.card S = 128 := by
    have h := (R.subgroupOf S).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe c.thompson_sylow).toEquiv, hi, hcR] at h
    exact h.symm
  have hcCS : Nat.card (S ⊓ C : Subgroup H) = 4 := by
    have h := f.ker.card_mul_index
    rw [index_ker, hf, sylow_card, hcS, hk] at h
    have he : Nat.card (C.subgroupOf S) = Nat.card (S ⊓ C : Subgroup H) := by
      rw [← card_map_of_injective S.subtype_injective, subgroupOf_map_subtype, inf_comm]
    rw [he] at h
    omega
  have hcB : Nat.card B = 4 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hB : B = S ⊓ C := eq_of_le_of_card_ge
    (inf_le_inf_right C c.thompson_sylow) (by rw [hcB, hcCS])
  obtain ⟨P, hP⟩ := c.S₁.exists_sylow_map_eq_inf_of_normal C
  let eP : P ≃* Multiplicative (ZMod 4) :=
    ((P : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).trans
      ((MulEquiv.subgroupCongr (hP.trans hB.symm)).trans eB)
  have hPc : IsCyclic P := isCyclic_of_injective eP.toMonoidHom eP.injective
  have hcP : Nat.card P = 4 := by
    rw [Nat.card_congr eP.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hoddC : pPrimeCore 2 C = ⊥ := by
    apply ((pPrimeCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp
    apply le_bot_iff.mp
    exact (pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 C).trans hodd.le
  have heven : 2 ∣ Nat.card C := (show 2 ∣ 4 by decide).trans
    (hcP ▸ (P : Subgroup C).card_subgroup_dvd_card)
  have hPt : (P : Subgroup C) = ⊤ := by
    have h := (P.isComplement'_pPrimeCore_of_isCyclic hPc heven).sup_eq_top
    change (P : Subgroup C) ⊔ pPrimeCore 2 C = ⊤ at h
    rwa [hoddC, sup_bot_eq] at h
  have hCB : C = B := by
    rw [hPt, ← MonoidHom.range_eq_map, C.range_subtype] at hP
    exact hP.trans hB.symm
  exact ⟨hCB.le.trans inf_le_left, ⟨(MulEquiv.subgroupCongr hCB).trans eB⟩⟩


/-- All later source36 steps and the terminal count follow from its actual
unique-involution statement, the original product coordinates, and source37. -/
theorem SourceComponentGeometry.false_of_unique_centralizer_involution
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (hi : (((sourceR d).subgroupOf (involutionCentralizer c.z)).subgroupOf
      (c.S₁ : Subgroup (involutionCentralizer c.z))).index = 2)
    (hx : c.x ∈ (c.S₁ : Subgroup (involutionCentralizer c.z)))
    (hodd : pPrimeCore 2 (involutionCentralizer c.z) = ⊥)
    (L : Subgroup (involutionCentralizer c.z)) (hLK : L ≤ c.K)
    (eL : L ≃* alternatingGroup (Fin 4))
    (huR : c.u ∈ (sourceR d).subgroupOf (involutionCentralizer c.z))
    (huL : c.u ∈ centralizer (L : Set (involutionCentralizer c.z)))
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (eC : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (L : Set (involutionCentralizer c.z)) : Subgroup (involutionCentralizer c.z)) ≃*
        (E × DihedralGroup 4))
    (hR : Nat.card (sourceR d) = Nat.card E * 64)
    (hu : ∃! z : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (c.K : Set (involutionCentralizer c.z)) : Subgroup (involutionCentralizer c.z)),
      orderOf z = 2)
    (hsR : c.s ∈ normalizer (sourceR d : Set G))
    (hsK : c.s^2 ∈ normalizer (c.K.map (involutionCentralizer c.z).subtype : Set G))
    (hzR : (c.z₁:G) ∈ centralizer (sourceR d : Set G))
    (hf : SourceElementarySixteenFusion c) : False := by
  obtain ⟨hE,⟨eB⟩⟩ := c.centralizer_cyclic_four_of_unique L hLK eL huR huL eC hu
  have hR64 : Nat.card (sourceR d) = 64 := by simpa only [hE,one_mul] using hR
  obtain ⟨hC,⟨eFull⟩⟩ := c.full_centralizer_of_cyclic_four hi hR64 hodd eB
  obtain ⟨P,hP⟩ := c.exists_component_sylow hi hx
  obtain ⟨f⟩ := c.exists_source_factors_of_pair_inputs hC eFull P hP hR64 hsR hsK hzR hf
  exact c.false_of_source_factors f

end CFSG.Quasithin.Chapter2.DoubleA3
