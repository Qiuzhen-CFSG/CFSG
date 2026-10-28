module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.ResidualLift
public import Stellmacher.SectionThree.ResidualActiveChiefSection
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.Representation.CubicClifford.Extension.Construction
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.FrobeniusExclusions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.Recognition.Linear
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces

/-!
# Chief sections and the two exceptional residual actions

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 8.2.9, final paragraph, printed p.721
(PDF p.738).

The source paragraph has three logically separate pieces.  First, a chief
section of the actual elementary abelian two-core is selected on which the
actual two-residual acts.  The construction below uses the literal quotient
and conjugation map, and proves the two-core kernel from chief irreducibility;
no family tag or preselected section is used.  Second, the standard Clifford
extension construction supplies the homogeneous tensor action and its actual
multiplicity representation.  Finally, the two small residual alternatives
are excluded: the L₂(31) case by the binary degree bound, and the
Aut(L₃(2)) case by the graph automorphism, since it interchanges the natural
and dual modules.

The remaining source work is the local input which identifies the elementary
abelian layer, supplies the extending constituent, and proves the rank-one
fixed-space bound for the element v⁺.  Those inputs belong to the assembly of
Lemma 8.2.9; these declarations retain them explicitly rather than replacing
them with a stronger conclusion.
-/

public section

open Subgroup
open Representation
open scoped Pointwise TensorProduct

namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction

/-- The two-core of the acting group is killed by an irreducible binary chief
section.  `hIrr` is the literal invariant-subgroup conclusion supplied by the
chief-section construction, and `hNontriv` prevents the vacuous zero section. -/
theorem chief_section_core_kernel
    {P W : Type*} [Group P] [Finite P] [Group W] [Finite W]
    (f : P →* MulAut W)
    (hElem : IsElementaryAbelian 2 W)
    (hNontriv : Nontrivial W)
    (hIrr : ∀ K : Subgroup W,
      (∀ p : P, ∀ w, w ∈ K → f p w ∈ K) → K = ⊥ ∨ K = ⊤) :
    pCore 2 P ≤ f.ker := by
  let _ : IsElementaryAbelian 2 W := hElem
  let _ : Nontrivial W := hNontriv
  apply irreducible_range_core_le_ker f
  intro K hK
  exact hIrr K (fun p w hw => by
    exact hK ⟨f p, ⟨p, rfl⟩⟩ w hw)

/-- The kernel containment above, written with the original quotient map.  This
is the form used when the source says that `O₂(H)` centralizes the chief
section: no identification of the quotient with an abstract module is made. -/
theorem core_centralizes_chief_section
    {X : Type*} [Group X] {P E D : Subgroup X}
    (_hDE : D ≤ E) (hPE : P ≤ normalizer (E : Set X))
    (hN : (D.subgroupOf E).Normal)
    (f : P →* MulAut (E ⧸ D.subgroupOf E))
    (hf : ∀ p : P, ∀ e : E,
      f p (QuotientGroup.mk' (D.subgroupOf E) e) =
        QuotientGroup.mk' (D.subgroupOf E)
          ⟨(p : X) * (e : X) * (p : X)⁻¹,
            (mem_normalizer_iff.mp (hPE p.property) e).mp e.property⟩)
    (hcore : pCore 2 P ≤ f.ker) :
    ∀ p : P, p ∈ pCore 2 P → ∀ e : E,
      QuotientGroup.mk' (D.subgroupOf E)
          ⟨(p : X) * (e : X) * (p : X)⁻¹,
            (mem_normalizer_iff.mp (hPE p.property) e).mp e.property⟩ =
        QuotientGroup.mk' (D.subgroupOf E) e := by
  let _ := hN
  intro p hp e
  have hfp : f p = 1 := MonoidHom.mem_ker.mpr (hcore hp)
  have he := hf p e
  rw [hfp] at he
  exact he.symm

/-- Construct the actual chief section moved by the two-residual.  The
quotient is `E / D` with its ambient normality instance, and `f` is literal
conjugation by `P`; the final conjunct records the action of `O₂(P)` on the
section.  The notation `twoResidualAmbient` is Stellmacher's ambient `O²`
construction and is kept distinct from the p-core. -/
theorem exists_moved_chief_section
    {X : Type*} [Group X] [Finite X] (P C : Subgroup X)
    (hCP : C ≤ P) (hCN : (C.subgroupOf P).Normal)
    (hC : IsElementaryAbelian 2 C)
    (hres : ⁅Stellmacher.twoResidualAmbient P, C⁆ ≠ ⊥) :
    ∃ E D : Subgroup X, ∃ _hEC : E ≤ C, ∃ _hDE : D ≤ E,
      ∃ hPE : P ≤ normalizer (E : Set X),
      ∃ _hPD : P ≤ normalizer (D : Set X),
      ∃ hN : (D.subgroupOf E).Normal,
      let _ := hN
      ∃ f : P →* MulAut (E ⧸ D.subgroupOf E),
        (∀ p : P, ∀ e : E,
          f p (QuotientGroup.mk' (D.subgroupOf E) e) =
            QuotientGroup.mk' (D.subgroupOf E)
              ⟨(p : X) * (e : X) * (p : X)⁻¹,
                (mem_normalizer_iff.mp (hPE p.property) e).mp e.property⟩) ∧
        IsElementaryAbelian 2 (E ⧸ D.subgroupOf E) ∧
        (∀ K : Subgroup (E ⧸ D.subgroupOf E),
          (∀ p : P, ∀ w, w ∈ K → f p w ∈ K) → K = ⊥ ∨ K = ⊤) ∧
        pCore 2 P ≤ f.ker ∧
        ¬Stellmacher.twoResidualSubgroup P ≤ f.ker := by
  obtain ⟨E, D, hEC, hDE, hPE, hPD, hN, f, hf, hElem, hIrr, hactive⟩ :=
    Stellmacher.SectionThree.exists_residual_active_chief_section P C hCP hCN hC hres
  let _ := hN
  have hNontriv : Nontrivial (E ⧸ D.subgroupOf E) := by
    by_contra h
    let _ : Subsingleton (E ⧸ D.subgroupOf E) :=
      not_nontrivial_iff_subsingleton.mp h
    apply hactive
    intro p hp
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro w
    exact Subsingleton.elim _ _
  have hcore := chief_section_core_kernel f hElem hNontriv hIrr
  exact ⟨E, D, hEC, hDE, hPE, hPD, hN, f, hf, hElem, hIrr, hcore, hactive⟩

/-- Clifford's extension construction, specialized to the binary setting used
in the chief-section argument.  It constructs the homogeneous multiplicity
representation and its tensor equivalence; the last inequality records the
source fact that at least two copies occur. -/
theorem multiplicity_representation_of_extension
    {H : Type*} [Group H] [Finite H]
    (Ksub : Subgroup H) [Ksub.Normal]
    {V E : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) H E)
    (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ]
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V]
    (hσabs : IsAbsolutelyIrreducible (τ.comp Ksub.subtype))
    (A : Subrepresentation (ρ.comp Ksub.subtype))
    (hA : Nonempty (Representation.Equiv A.toRepresentation (τ.comp Ksub.subtype)))
    (hEpos : 0 < Module.finrank (ZMod 2) E)
    (hlarge : 2 * Module.finrank (ZMod 2) E ≤ Module.finrank (ZMod 2) V) :
    IsIrreducible (Representation.CubicClifford.homRepresentation Ksub τ ρ) ∧
      Ksub ≤ (Representation.CubicClifford.homRepresentation Ksub τ ρ).ker ∧
      Nonempty (Representation.Equiv ρ
        (τ.tprod (Representation.CubicClifford.homRepresentation Ksub τ ρ))) ∧
      2 ≤ Module.finrank (ZMod 2)
        (Representation.CubicClifford.homSpace Ksub τ ρ) := by
  let μ := Representation.CubicClifford.homRepresentation Ksub τ ρ
  have hd := Representation.CubicClifford.extension_tensor_decomposition
    Ksub τ ρ hσabs A hA
  obtain ⟨e⟩ := hd.2.2
  have he := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct] at he
  have hmul : 2 * Module.finrank (ZMod 2) E ≤
      Module.finrank (ZMod 2) E * Module.finrank (ZMod 2)
        (Representation.CubicClifford.homSpace Ksub τ ρ) := by
    exact hlarge.trans_eq he
  have hmult : 2 ≤ Module.finrank (ZMod 2)
      (Representation.CubicClifford.homSpace Ksub τ ρ) := by
    apply Nat.le_of_mul_le_mul_left (c := Module.finrank (ZMod 2) E)
    · simpa [Nat.mul_comm] using hmul
    · exact hEpos
  exact ⟨hd.1, hd.2.1, hd.2.2, hmult⟩

/-- The Frobenius subgroup in PSL₂(31) forces binary degree at least fifteen,
so it cannot act faithfully on a chief section of degree at most eight. -/
theorem exclude_psl2_thirtyOne_of_degree_le_eight
    {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ)
    (hmodel : ClassicalGroup.IsPSL G 2 31)
    (hdim : Module.finrank (ZMod 2) V ≤ 8) : False := by
  have h := CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.psl2_thirtyOne_degree_ge_fifteen ρ hρ hmodel
  omega

/-- The rank-one displacement estimate is converted to the fixed-codimension
input of the checked binary SL₃(2) recognition theorem.  No natural marking is
assumed: `linear_split` constructs it. -/
theorem natural_module_of_rank_one_involution
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (hρ : Function.Injective ρ)
    (t : BinaryLinearThree.Group) (ht : t ^ 2 = 1) (hne : t ≠ 1)
    (hdisp : Module.finrank (ZMod 2)
        (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    ∃ (e : Multiplicative (CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments.moving ρ).toSubmodule
        ≃* Multiplicative (Fin 3 → ZMod 2))
      (marking : BinaryLinearThree.Group ≃* BinaryLinearThree.Group),
      (∀ g v,
        (e (Multiplicative.ofAdd
          ((CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments.moving ρ).toRepresentation g v))).toAdd =
          (marking g).val.mulVec
            (e (Multiplicative.ofAdd v)).toAdd) ∧
      IsCompl
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments.moving ρ).toSubmodule
        (Representation.BinaryOffender.fixedSpace ρ ⊤) := by
  have hsmall : Representation.BinaryOffender.fixedCodim ρ (zpowers t) ≤ 1 := by
    rw [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank]
    exact hdisp
  exact CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Recognition.linear_split
    ρ hρ t ht hne hsmall

/-- Every nonidentity involution in the concrete binary L₃(2) is conjugate to
the displayed elementary transvection. -/
theorem binary_involution_conjugate_to_transvection
    (t : BinaryLinearThree.Group) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    ∃ g : BinaryLinearThree.Group, t * g =
      g * BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution := by
  apply BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator t hne
  simpa [pow_two] using ht

/-- The graph automorphism cannot stabilize the binary natural module.  Its
natural twist is the dual module, and the two actual representations are
inequivalent. -/
theorem no_graph_extension_of_natural :
    ¬ Nonempty (Representation.Equiv
      (BinaryLinearThree.W.comp BinaryLinearThree.AutomorphismAction.graph.toMonoidHom)
      BinaryLinearThree.W) := by
  intro h
  apply BinaryLinearThree.AutomorphismAction.natural_not_equiv_dual
  obtain ⟨e⟩ := h
  exact ⟨e.symm.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual⟩

/-- More generally, no outer automorphism of the concrete L₃(2) can stabilize
its natural module.  This is the action-level incompatibility used for the
Aut(L₃(2)) alternative. -/
theorem no_outer_extension_of_natural
    (a : MulAut BinaryLinearThree.Group)
    (ha : a ∉ MulAut.innerSubgroup BinaryLinearThree.Group) :
    ¬ Nonempty (Representation.Equiv
      (BinaryLinearThree.W.comp a.toMonoidHom) BinaryLinearThree.W) := by
  intro h
  apply BinaryLinearThree.AutomorphismAction.natural_not_equiv_dual
  obtain ⟨e⟩ := h
  exact ⟨e.symm.trans
    (BinaryLinearThree.AutomorphismAction.naturalOuterEquiv a ha)⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction
