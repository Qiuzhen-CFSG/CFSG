module
public import Theory.Representation.AlternatingSixInvolutionDegree
public import Theory.Representation.HexacodeAction.EvenBinaryRecognition
public import Theory.Representation.HexacodeAction.FaithfulDegrees
public import Theory.Representation.PerfectInvolutionExtension
public import Theory.Representation.HexacodeAction.CentralCharacter
public import Theory.Representation.HexacodeAction.OvergroupFitting
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.SimpleHeadQuotient
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.Representation.PSL3Two.ResidualFFForms.Descent

/-!
# Small involution budgets above the even hexacode cover

Three conjugates of each involution generate the actual triple cover: their
images generate A6, and a central supplement cannot enlarge a subgroup of a
perfect group. A nontrivial simple binary module with displacement at most
two therefore has degree four or six. The existing small-degree and faithful
cover classifications identify the two possible kernels.

The same involution costs at least two dimensions in every nontrivial simple
module above the full hexacode group with a two-group kernel. Restriction to
the even preimage and descent are performed only on simple constituents.
Consequently a fully moved module with zero fixed space and total cost at
most two is irreducible, even if the two-group kernel initially acts on a
nonsplit extension. The application is the original exceptional moving
radius in MS93 (3.8), printed pp.878--879.

The concrete hexacode model and its finite recognition retain the ATLAS
attribution and license in the imported modules.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace Representation.Hexacode.SmallInvolution

/-- The odd cubic kernel cannot kill an involution. -/
theorem coordinate_involution (t : HexEvenAutomorphisms) (ht : orderOf t = 2) :
    orderOf (hexEvenCoordinate t) = 2 := by
  apply orderOf_eq_prime
  · rw [←map_pow,←ht,pow_orderOf_eq_one,map_one]
  · intro he
    have hm : t ∈ center HexEvenAutomorphisms := even_kernel_eq_center ▸ he
    have hd := orderOf_dvd_natCard (⟨t,hm⟩ : center HexEvenAutomorphisms)
    rw [Subgroup.orderOf_mk,ht,even_center_card] at hd
    norm_num at hd

/-- Three conjugates generate the entire cover, including its cubic center. -/
theorem exists_three_conjugate_generators (t : HexEvenAutomorphisms)
    (ht : orderOf t = 2) :
    ∃ c : Fin 3 → HexEvenAutomorphisms,
      closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  obtain ⟨d,hd⟩ := AlternatingSix.InvolutionDisplacement.exists_three_conjugate_generators
    (hexEvenCoordinate t) (coordinate_involution t ht)
  choose c hc using fun i => hexEvenCoordinate_surjective (d i)
  refine ⟨c,?_⟩
  let U := closure (Set.range fun i => c i * t * (c i)⁻¹)
  have hmap : U.map hexEvenCoordinate = ⊤ := by
    change (Subgroup.closure _).map hexEvenCoordinate = ⊤
    rw [MonoidHom.map_closure]
    have he : hexEvenCoordinate '' (Set.range fun i => c i * t * (c i)⁻¹) =
        Set.range (fun i => d i * hexEvenCoordinate t * (d i)⁻¹) := by
      ext x
      simp only [Set.mem_image,Set.mem_range]
      constructor
      · rintro ⟨_,⟨i,rfl⟩,rfl⟩
        exact ⟨i,by simp [hc]⟩
      · rintro ⟨i,rfl⟩
        exact ⟨_,⟨i,rfl⟩,by simp [hc]⟩
    rw [he,hd]
  let := even_isPerfect
  apply eq_top_of_sup_center_eq_top U
  have hh := congrArg (Subgroup.comap hexEvenCoordinate) hmap
  rwa [comap_map_eq,even_kernel_eq_center,comap_top] at hh

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Zero fixed space bounds degree by three times one involution displacement. -/
theorem finrank_le_three_mul (ρ : Representation (ZMod 2) HexEvenAutomorphisms W)
    (hfixed : fixedSpace ρ ⊤ = ⊥) (t : HexEvenAutomorphisms) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) W ≤ 3 * fixedCodim ρ (zpowers t) := by
  obtain ⟨c,hc⟩ := exists_three_conjugate_generators t ht
  exact finrank_le_mul_fixedCodim_of_conjugate_generation ρ ⊤ hfixed t c hc.ge

omit [FiniteDimensional (ZMod 2) W] in
/-- A nontrivial simple action has no global fixed vectors. -/
theorem simple_fixedSpace_eq_bot (ρ : Representation (ZMod 2) HexEvenAutomorphisms W)
    [IsIrreducible ρ] (hne : ρ ≠ 1) : fixedSpace ρ ⊤ = ⊥ := by
  by_contra hn
  have hk := ρ.le_ker_of_normal_invariants_ne_bot ⊤ hn
  exact hne (MonoidHom.ext (fun g => hk (mem_top g)))

/-- The affordable simple cover modules have natural degree four or faithful degree six. -/
theorem simple_degree (ρ : Representation (ZMod 2) HexEvenAutomorphisms W)
    [IsIrreducible ρ] (hne : ρ ≠ 1)
    (t : HexEvenAutomorphisms) (ht : orderOf t = 2)
    (hcost : fixedCodim ρ (zpowers t) ≤ 2) :
    (center HexEvenAutomorphisms ≤ ρ.ker ∧ Module.finrank (ZMod 2) W = 4) ∨
      (Function.Injective ρ ∧ Module.finrank (ZMod 2) W = 6) := by
  let := even_isPerfect
  have hd : Module.finrank (ZMod 2) W ≤ 6 := by
    have hh := finrank_le_three_mul ρ (simple_fixedSpace_eq_bot ρ hne) t ht
    omega
  by_cases hz : center HexEvenAutomorphisms ≤ ρ.ker
  · let σ := (quotientOfLEKer ρ (center HexEvenAutomorphisms) hz).comp
      even_quotient_center_equiv.symm.toMonoidHom
    let : IsIrreducible σ := (irreducible_comp_surjective_iff
      even_quotient_center_equiv.symm.toMonoidHom even_quotient_center_equiv.symm.surjective _).mpr
      ((quotientOfLEKer_irreducible_iff ρ _ hz).mpr inferInstance)
    rcases AlternatingSix.BinarySmallDegrees.finrank_eq_one_or_four σ hd with hdim | hdim
    · have hsmall := PerfectInvolutionExtension.small_action_trivial ρ (by omega)
      exact (hne (MonoidHom.ext (fun g => LinearMap.ext (hsmall g)))).elim
    · exact Or.inl ⟨hz,hdim⟩
  · have hf := faithful_of_center_not_le_ker ρ hz
    have hh := TwelveDimensional.faithful_finrank_six_or_eighteen ρ hf
    change Module.finrank (ZMod 2) W = 6 ∨ Module.finrank (ZMod 2) W = 18 at hh
    exact Or.inr ⟨hf,by omega⟩

/-- Every involution costs at least two dimensions on a nontrivial simple cover module. -/
theorem simple_fixedCodim_lower (ρ : Representation (ZMod 2) HexEvenAutomorphisms W)
    [IsIrreducible ρ] (hne : ρ ≠ 1)
    (t : HexEvenAutomorphisms) (ht : orderOf t = 2) :
    2 ≤ fixedCodim ρ (zpowers t) := by
  by_contra hn
  have hc : fixedCodim ρ (zpowers t) ≤ 2 := by omega
  have hd := simple_degree ρ hne t ht hc
  have hb := finrank_le_three_mul ρ (simple_fixedSpace_eq_bot ρ hne) t ht
  rcases hd with hd | hd <;> omega

section Projected
variable {H : Type*} [Group H] [Finite H]

/-- The two-dimensional constituent cost survives an arbitrary two-group kernel. -/
theorem projected_simple_fixedCodim_lower
    (π : H →* HexAutomorphisms) (hE : hexSign.ker ≤ π.range)
    (hp : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ] (hne : ρ ≠ 1)
    (A : Subgroup H) (hAE : A.map π ≤ hexSign.ker)
    (t : HexEvenAutomorphisms) (ht : orderOf t = 2) (htA : t.val ∈ A.map π) :
    2 ≤ fixedCodim ρ A := by
  let P := evenPreimage π
  let q : P →* HexEvenAutomorphisms := {
    toFun x := ⟨π x,x.property⟩
    map_one' := Subtype.ext (map_one π)
    map_mul' x y := Subtype.ext (map_mul π x.val y.val) }
  have hq : Function.Surjective q := by
    intro g
    obtain ⟨x,hx⟩ := hE g.property
    exact ⟨⟨x,by change hexSign (π x) = 1; rw [hx]; exact g.property⟩,Subtype.ext hx⟩
  have hqker : q.ker = π.ker.comap P.subtype := by
    ext x
    exact Subtype.ext_iff
  have hpq : IsPGroup 2 q.ker := by
    rw [hqker]
    exact hp.comap_subtype
  have hAP : A ≤ P := fun x hx => hAE (mem_map_of_mem π hx)
  have hnP : ¬ P ≤ ρ.ker := by
    intro hk
    let σ := quotientOfLEKer ρ P hk
    let : IsIrreducible σ := (quotientOfLEKer_irreducible_iff ρ P hk).mpr inferInstance
    have hpk := normal_p_subgroup_le_ker σ (⊤ : Subgroup (H ⧸ P))
      ((quotient_evenPreimage_isTwoGroup π).to_subgroup ⊤)
    apply hne
    ext g v
    exact LinearMap.congr_fun (hpk (mem_top (QuotientGroup.mk' P g))) v
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp P.subtype)
  let := hJ
  have hnJ : J.toRepresentation ≠ 1 := by
    intro hj
    apply hnP
    apply ρ.le_ker_of_normal_invariants_ne_bot P
    intro hz
    have hle : J.toSubmodule ≤ Representation.invariants (ρ.comp P.subtype) := by
      intro v hv g
      exact congrArg Subtype.val (LinearMap.congr_fun
        (congrArg (fun σ => σ g) hj) ⟨v,hv⟩)
    have hbot : J = ⊥ := Subrepresentation.toSubmodule_injective
      (le_bot_iff.mp (hz ▸ hle))
    exact ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot hbot
  let σ := BinaryLinearThree.ResidualFFForms.irreducibleDescent q hq hpq J.toRepresentation
  have hcomp : σ.comp q = J.toRepresentation :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_comp q hq hpq J.toRepresentation
  let : IsIrreducible σ :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_irreducible q hq hpq J.toRepresentation
  have hnσ : σ ≠ 1 := by
    intro hs
    apply hnJ
    rw [←hcomp,hs]
    rfl
  have htq : t ∈ (A.subgroupOf P).map q := by
    obtain ⟨x,hx,hxt⟩ := htA
    exact ⟨⟨x,hAP hx⟩,hx,Subtype.ext hxt⟩
  have hl := simple_fixedCodim_lower σ hnσ t ht
  have hmono : fixedCodim σ (zpowers t) ≤ fixedCodim σ ((A.subgroupOf P).map q) := by
    have hh := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr htq))
    have h₁ := fixedCodim_add_finrank σ (zpowers t)
    have h₂ := fixedCodim_add_finrank σ ((A.subgroupOf P).map q)
    omega
  have he : fixedCodim σ ((A.subgroupOf P).map q) =
      fixedCodim J.toRepresentation (A.subgroupOf P) := by
    rw [←hcomp]
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  have hsub := fixedCodim_subrepresentation_le (ρ.comp P.subtype) J (A.subgroupOf P)
  rw [fixedCodim_subgroupOf ρ hAP] at hsub
  omega

omit [FiniteDimensional (ZMod 2) W] [Finite H] in
private theorem full_quotient (ρ : Representation (ZMod 2) H W)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (N : Subrepresentation ρ) :
    subspaceCommutator N.quotientRepresentation ⊤ ⊤ = ⊤ := by
  have h : subspaceCommutator ρ ⊤ ⊤ ≤
      (subspaceCommutator N.quotientRepresentation ⊤ ⊤).comap N.toSubmodule.mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    change N.toSubmodule.mkQ (ρ g v - v) ∈ subspaceCommutator N.quotientRepresentation ⊤ ⊤
    rw [map_sub,←N.quotientRepresentation_mk]
    exact Submodule.subset_span ⟨g,hg,N.toSubmodule.mkQ v,Submodule.mem_top,rfl⟩
  rw [hfull] at h
  apply top_unique
  intro q _
  obtain ⟨v,rfl⟩ := N.toSubmodule.mkQ_surjective q
  exact h Submodule.mem_top

omit [FiniteDimensional (ZMod 2) W] [Finite H] in
private theorem nontrivial_of_full [Nontrivial W]
    (ρ : Representation (ZMod 2) H W)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) : ρ ≠ 1 := by
  intro he
  have hz : subspaceCommutator ρ ⊤ ⊤ ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    simp [he]
  rw [hfull] at hz
  exact top_ne_bot (le_bot_iff.mp hz)

/-- A fully moved fixed-point-free module of total cost two has just one simple constituent. -/
theorem projected_irreducible
    (π : H →* HexAutomorphisms) (hE : hexSign.ker ≤ π.range)
    (hp : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) H W) [Nontrivial W]
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup H) (hAE : A.map π ≤ hexSign.ker)
    (t : HexEvenAutomorphisms) (ht : orderOf t = 2) (htA : t.val ∈ A.map π)
    (hcost : fixedCodim ρ A ≤ 2) : IsIrreducible ρ := by
  obtain ⟨N,hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  let := hN
  let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
  have hn : N.toRepresentation ≠ 1 := by
    intro he
    obtain ⟨v,hv⟩ := exists_ne (0 : N.toSubmodule)
    apply hv
    apply Subtype.ext
    have hh : v.val ∈ fixedSpace ρ ⊤ := by
      intro g
      exact congrArg Subtype.val (LinearMap.congr_fun
        (congrArg (fun σ => σ g.val) he) v)
    change v.val = 0
    simpa only [hfix,Submodule.mem_bot] using hh
  have hlo := projected_simple_fixedCodim_lower π hE hp N.toRepresentation hn A hAE t ht htA
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ N A
  have hzero : fixedCodim N.quotientRepresentation A = 0 := by omega
  have htop : N = ⊤ := by
    by_contra hne
    have hnsub : N.toSubmodule ≠ ⊤ := fun he => hne (Subrepresentation.toSubmodule_injective he)
    let : Nontrivial (W ⧸ N.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hnsub
    let : IsCoatomic (Subrepresentation N.quotientRepresentation) :=
      SimpleHeadQuotient.subrepresentation_coatomic _
    obtain ⟨D,hD,_⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation N.quotientRepresentation)).resolve_left bot_ne_top
    let := SimpleHeadQuotient.irreducible_quotient_of_isCoatom D hD
    let := Subrepresentation.irreducible_module_nontrivial D.quotientRepresentation
    have hd := full_quotient N.quotientRepresentation (full_quotient ρ hfull N) D
    have hlow := projected_simple_fixedCodim_lower π hE hp D.quotientRepresentation
      (nontrivial_of_full D.quotientRepresentation hd) A hAE t ht htA
    have hupper := fixedCodim_quotient_add_subrepresentation_le N.quotientRepresentation D A
    omega
  exact isSimpleOrder_iff_isAtom_top.mpr
    (htop ▸ (Subrepresentation.irreducible_iff_isAtom N).mp hN)

end Projected
end Representation.Hexacode.SmallInvolution
