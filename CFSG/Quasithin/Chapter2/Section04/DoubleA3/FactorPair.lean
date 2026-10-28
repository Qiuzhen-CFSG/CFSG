module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.PureFusion
public import Theory.GroupTheory.DihedralConjugatePair

/-!
# The actual conjugate dihedral factors in the paired-cubic source

The component Sylow R ∩ K has order eight and is normal in the original
Thompson subgroup R. The original element s normalizes R, and its square
normalizes the ambient component. If the two conjugate Sylow factors met
nontrivially, their normal intersection would contain the unique central
involution z₁ of the first factor. Conjugating would put z₂ in K, which is
impossible because K is centerless and lies in C_G(z₂).

Thus the literal right conjugate is disjoint from R ∩ K. Both factors are
normal in R, so they commute; their orders and |R| = 64 give generation.
The final constructor fills the frozen source-factor record using these
facts, the preceding six-point fusion bound, and the independently supplied
centralizer calculation from source 2.4.36(2).

Source: Aschbacher–Smith, 2.4.36(1) and 2.4.37, printed pp.549–550,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Subgroup Stellmacher AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original right-conjugate Sylow factors form the required direct product.
Their disjointness follows from movement of the unique dihedral center. -/
theorem SourceComponentGeometry.exists_factor_pair
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (P : Sylow 2 c.K)
    (hP : (P : Subgroup c.K).map c.K.subtype =
      (sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K)
    (hRcard : Nat.card (sourceR d)=64)
    (hsR : c.s ∈ normalizer (sourceR d : Set G))
    (hsK : c.s^2 ∈ normalizer (c.K.map (involutionCentralizer c.z).subtype : Set G))
    (hzR : (c.z₁:G) ∈ centralizer (sourceR d : Set G)) :
    ∃ E : Subgroup (involutionCentralizer c.z),
      E.map (involutionCentralizer c.z).subtype =
        (((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K).map
          (involutionCentralizer c.z).subtype).map (MulAut.conj c.s⁻¹).toMonoidHom ∧
      ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) ⊔ E =
        (sourceR d).subgroupOf (involutionCentralizer c.z) ∧
      Disjoint ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) E ∧
      ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) ≤
        centralizer (E : Set (involutionCentralizer c.z)) := by
  let H := involutionCentralizer c.z
  let R := sourceR d
  let K := c.K.map H.subtype
  let D₀ := R.subgroupOf H ⊓ c.K
  let D := R ⊓ K
  have hDmap : D₀.map H.subtype=D := by
    rw [map_inf _ _ _ H.subtype_injective,map_subgroupOf_eq_of_le c.thompson_le]
  obtain ⟨eP⟩ := exists_component_sylow_coordinates c.K c.componentEquiv P
  let e₀ : D₀ ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hP.symm).trans eP
  let eD : D ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hDmap.symm).trans
    ((D₀.equivMapOfInjective H.subtype H.subtype_injective).symm.trans e₀)
  have hHK : H ≤ normalizer (K:Set G) := by
    have hh := c.K.le_normalizer_map H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,H.range_subtype] at hh
    exact hh
  have hRD : R ≤ normalizer (D:Set G) :=
    (le_inf R.le_normalizer (c.thompson_le.trans hHK)).trans inf_normalizer_le_normalizer_inf
  have hsD : c.s^2 ∈ normalizer (D:Set G) :=
    inf_normalizer_le_normalizer_inf ⟨(normalizer (R:Set G)).pow_mem hsR 2,hsK⟩
  have hzD : (c.z₁:G) ∈ D :=
    ⟨c.first_in_thompson,mem_map_of_mem H.subtype c.first_in_component⟩
  have hz₁1 : (c.z₁:G)≠1 := by
    intro he
    have hh := c.exchange
    rw [he,mul_one,inv_mul_cancel] at hh
    exact c.nonidentity hh.symm
  have hzK : c.z ∉ K := by
    rintro ⟨k,hk,hkg⟩
    have hcent : (⟨k,hk⟩ : c.K) ∈ center c.K := by
      rw [mem_center_iff]
      intro u
      apply Subtype.ext
      apply Subtype.ext
      change (u.val:G)*(k:G)=(k:G)*(u.val:G)
      calc
        (u.val:G)*(k:G) = (u.val:G)*c.z := congrArg (fun a : G => (u.val:G)*a) hkg
        _ = c.z*(u.val:G) := mem_centralizer_singleton_iff.mp u.val.property
        _ = (k:G)*(u.val:G) := congrArg (fun a : G => a*(u.val:G)) hkg.symm
    have he := (centerCongr c.componentEquiv ⟨⟨k,hk⟩,hcent⟩).property
    change c.componentEquiv ⟨k,hk⟩ ∈ center A6 at he
    have he0 : center A6 = ⊥ := alternatingGroup.center_eq_bot (by simp)
    rw [he0,mem_bot] at he
    have hk1 : k=1 := congrArg Subtype.val (c.componentEquiv.injective (he.trans c.componentEquiv.map_one.symm))
    exact c.nonidentity (hkg.symm.trans (congrArg Subtype.val hk1))
  have hpair := Theory.GroupTheory.dihedral_conjugate_pair_of_moved_center R D inf_le_left hRD eD hRcard
    c.s⁻¹ ((normalizer (R:Set G)).inv_mem hsR)
    (by simpa only [inv_pow] using (normalizer (D:Set G)).inv_mem hsD)
    c.z₁ hzD hz₁1 (centralizer_le inf_le_left hzR)
    (by rw [inv_inv,c.exchange]; exact fun hh => hzK hh.2)
  let E₀ := D.map (MulAut.conj c.s⁻¹).toMonoidHom
  have hE₀R : E₀ ≤ R := hpair.1 ▸ (show E₀ ≤ D ⊔ E₀ from le_sup_right)
  have hE₀H : E₀ ≤ H := hE₀R.trans c.thompson_le
  let E := E₀.subgroupOf H
  have hEmap : E.map H.subtype=E₀ := map_subgroupOf_eq_of_le hE₀H
  refine ⟨E,?_,?_,?_,?_⟩
  · rw [hEmap,hDmap]
  · apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hDmap,hEmap,map_subgroupOf_eq_of_le c.thompson_le]
    exact hpair.1
  · apply disjoint_def.mpr
    intro a haD haE
    apply Subtype.ext
    exact disjoint_def.mp hpair.2.1 (hDmap ▸ mem_map_of_mem H.subtype haD) haE
  · intro a haD b hbE
    apply Subtype.ext
    exact hpair.2.2 (hDmap ▸ mem_map_of_mem H.subtype haD) b.val hbE

/-- The actual factor pair plus the centralizer and elementary fusion inputs
constructs the frozen terminal source record. -/
theorem SourceComponentGeometry.exists_source_factors_of_pair_inputs
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (hcentralizer : centralizer (c.K : Set (involutionCentralizer c.z)) ≤
      (sourceR d).subgroupOf (involutionCentralizer c.z))
    (eB : centralizer (c.K : Set (involutionCentralizer c.z)) ≃* Multiplicative (ZMod 4))
    (P : Sylow 2 c.K)
    (hP : (P : Subgroup c.K).map c.K.subtype =
      (sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K)
    (hRcard : Nat.card (sourceR d)=64)
    (hsR : c.s ∈ normalizer (sourceR d : Set G))
    (hsK : c.s^2 ∈ normalizer (c.K.map (involutionCentralizer c.z).subtype : Set G))
    (hzR : (c.z₁:G) ∈ centralizer (sourceR d : Set G))
    (hlocal : SourceElementarySixteenFusion c) : Nonempty (SourceFactorGeometry c) := by
  obtain ⟨E,hE,hgen,hd,hc⟩ := c.exists_factor_pair P hP hRcard hsR hsK hzR
  exact ⟨c.sourceFactors_of_elementary_sixteen_fusion hcentralizer eB P hP E hE hgen hd hc hlocal⟩

end CFSG.Quasithin.Chapter2.DoubleA3
