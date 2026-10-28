module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Splitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The binary SL₃ extension exclusions in B.5.1

The checked concrete central-attachment theorem supplies the missing endpoint
of the doubled-natural splitting argument. Its involution proof makes a
nontrivial upper attachment exceed the FF budget. The same theorem excludes
simultaneous nontrivial upper and lower attachments, yielding the fixed-kernel
condition of B.5.1(5) when the whole actor is SL₃(2).

We transport only this intrinsic matrix-group result from the earlier checked
Chapter C development: its proof uses explicit cocycles and involutions, not
B.5.1 or a classification premise. The moved and fixed spaces below are
literally those in the original representation. Field transport identifies any
binary field of degree one with ZMod 2 and retains a common marking on both
copies. Together with cohomology for larger fields, this covers every positive
binary degree.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(3)–(4),
printed p.91, and B.5.1(2),(5), printed pp.102–103. The reused intrinsic proofs
are in `ChapterC/.../ModuleAlternatives/CentralAttachments`.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
  {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem invariants_relabel (e : G ≃* H) :
    Representation.invariants (ρ.comp e.symm.toMonoidHom) = ρ.invariants := by
  ext v
  constructor
  · intro hv g
    have h := hv (e g)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using h
  · intro hv g
    exact hv (e.symm g)

theorem moved_relabel (e : G ≃* H) :
    moved (ρ.comp e.symm.toMonoidHom) ⊤ = moved ρ ⊤ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    exact Submodule.subset_span ⟨e.symm g, Subgroup.mem_top _, v, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    refine Submodule.subset_span ⟨e g, Subgroup.mem_top _, v, Submodule.mem_top, ?_⟩
    simp

theorem source_isFF [Finite G] {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) : IsFFModule ρ := by
  let := h.finite_module
  let := h.quasisimple
  let : Nontrivial (L ⧸ Subgroup.center L) := h.quasisimple.simple.toNontrivial
  let : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  let : Nontrivial G := L.subtype_injective.nontrivial
  by_contra hn
  have hj : offenderSubgroup ρ = ⊥ := by
    apply bot_unique
    apply iSup₂_le
    intro A hA
    exact False.elim (hn ⟨A, hA.1.isOffender ρ⟩)
  rw [h.generated] at hj
  exact top_ne_bot hj

open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition

private theorem moving_relabel_eq (s : MovedSection ρ ⊤) (e : G ≃* SL) :
    (CentralAttachments.moving (ρ.comp e.symm.toMonoidHom)).toSubmodule = s.space.toSubmodule := by
  exact (CentralAttachments.moving_eq _).trans ((moved_relabel e).trans s.space_eq.symm)

private noncomputable def moving_relabel_equiv (s : MovedSection ρ ⊤) (e : G ≃* SL) :
    (CentralAttachments.moving (ρ.comp e.symm.toMonoidHom)).toSubmodule ≃ₗ[ZMod 2]
      s.space.toSubmodule := LinearEquiv.ofEq _ _ (moving_relabel_eq s e)

private theorem moving_relabel_equivariant (s : MovedSection ρ ⊤) (e : G ≃* SL)
    (g : SL) (v : (CentralAttachments.moving (ρ.comp e.symm.toMonoidHom)).toSubmodule) :
    moving_relabel_equiv s e
      ((CentralAttachments.moving (ρ.comp e.symm.toMonoidHom)).toRepresentation g v) =
      s.space.toRepresentation (e.symm g) (moving_relabel_equiv s e v) := by
  apply Subtype.ext
  rfl

theorem binary_double_isCompl [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hL : L = ⊤) (hFF : IsFFModule ρ)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) :
    IsCompl s.space.toSubmodule ρ.invariants := by
  subst L
  let e' : ActionEquiv s.space.toRepresentation
    (repeated (specialLinearNatural (k := ZMod 2) 3) 2) := e.ofTop
  let E : G ≃* SL := e'.groupEquiv
  let σ : Representation (ZMod 2) SL V := ρ.comp E.symm.toMonoidHom
  have hσ : IsFFModule σ := hFF.map_equivariant ρ σ E.toMonoidHom E.injective
    (LinearEquiv.refl (ZMod 2) V) (fun g v => by
      change ρ g v = ρ (E.symm (E g)) v
      rw [E.symm_apply_apply])
  let q := moving_relabel_equiv s E
  let c : CentralAttachments.Copies (CentralAttachments.moving σ).toRepresentation 2 :=
    { marking := MulEquiv.refl SL
      equiv := q.trans e'.linearEquiv
      equivariant := by
        intro g v i
        change e'.linearEquiv (q ((CentralAttachments.moving σ).toRepresentation g v)) i = _
        have hq := moving_relabel_equivariant s E g v
        change q ((CentralAttachments.moving σ).toRepresentation g v) = _ at hq
        rw [hq, e'.intertwines]
        change (specialLinearNatural (k := ZMod 2) 3) (E (E.symm g)) _ = _
        rw [E.apply_symm_apply]
        rfl }
  have hc := (CentralAttachments.doubled_isCompl hσ c).symm
  change IsCompl (CentralAttachments.moving (ρ.comp E.symm.toMonoidHom)).toSubmodule
    (fixedSpace (ρ.comp E.symm.toMonoidHom) ⊤) at hc
  rwa [moving_relabel_eq s E, fixedSpace_top, invariants_relabel] at hc

theorem binary_fixed_kernel_of_no_supplement [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ ⊤) (E : G ≃* SL) (hfaith : Function.Injective ρ)
    (hFF : IsFFModule ρ) (hns : s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤) :
    s.space.toSubmodule ⊓ ρ.invariants = ⊥ := by
  let σ : Representation (ZMod 2) SL V := ρ.comp E.symm.toMonoidHom
  have hσ : IsFFModule σ := hFF.map_equivariant ρ σ E.toMonoidHom E.injective
    (LinearEquiv.refl (ZMod 2) V) (fun g v => by
      change ρ g v = ρ (E.symm (E g)) v
      rw [E.symm_apply_apply])
  have hf : Function.Injective σ := hfaith.comp E.symm.injective
  have hnot : CentralAttachments.centralSum σ ≠ ⊤ := by
    simpa only [CentralAttachments.centralSum, σ, moving_relabel_eq s E, fixedSpace_top,
      invariants_relabel, sup_comm] using hns
  have hc := CentralAttachments.classification σ hf hσ
  rcases hc with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
  · exact False.elim (hnot (codisjoint_iff.mp hc.codisjoint))
  · exact False.elim (hnot (codisjoint_iff.mp hc.codisjoint))
  · exact False.elim (hnot hc)
  · have hz := disjoint_iff.mp hc.symm
    simpa only [σ, moving_relabel_eq s E, fixedSpace_top, invariants_relabel] using hz

/-- Field transport at the binary endpoint retains the natural action. -/
noncomputable def degreeOneNaturalEquiv (F : BinaryField) (hF : F.degree = 1) (d : ℕ) :
    ActionEquiv (linearNatural F d) (linearNatural BinaryField.two d) := by
  letI := Fintype.ofFinite F.Carrier
  have hc : Fintype.card F.Carrier = 2 := by
    rw [← Nat.card_eq_fintype_card, F.card_eq, hF]
    decide
  let e : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two hc).symm
  let l : F.Carrier ≃ₗ[ZMod 2] ZMod 2 :=
    { e.toAddEquiv with map_smul' := ZMod.map_smul e }
  refine ⟨Atlas.fieldEquivSL d e, LinearEquiv.piCongrRight (fun _ : Fin d => l), ?_⟩
  intro g v
  funext i
  change e (∑ j, g.val i j * v j) = ∑ j, e (g.val i j) * e (v j)
  simp only [map_sum, map_mul]

/-- Both copies use the same field and actor identification. -/
noncomputable def degreeOneRepeatedEquiv (F : BinaryField) (hF : F.degree = 1) (d r : ℕ) :
    ActionEquiv (repeated (linearNatural F d) r)
      (repeated (linearNatural BinaryField.two d) r) :=
  let e := degreeOneNaturalEquiv F hF d
  ⟨e.groupEquiv, LinearEquiv.piCongrRight (fun _ : Fin r => e.linearEquiv),
    fun g v => funext (fun i => e.intertwines g (v i))⟩

/-- No degree restriction is needed in the doubled SL₃ branch. -/
theorem doubleThree_isCompl [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (F : BinaryField) (hL : L = ⊤)
    (hFF : IsFFModule ρ)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F 3) 2)) : IsCompl s.space.toSubmodule ρ.invariants := by
  by_cases hF : 1 < F.degree
  · exact doubleThree_large_isCompl s F hF hL e
  have hF : F.degree = 1 := by have h := F.degree_pos; omega
  let q := degreeOneRepeatedEquiv F hF 3 2
  let e' : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural BinaryField.two 3) 2) :=
    ⟨e.groupEquiv.trans q.groupEquiv, e.linearEquiv.trans q.linearEquiv,
      fun g v => (congrArg q.linearEquiv (e.intertwines g v)).trans
        (q.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩
  exact binary_double_isCompl s hL hFF e'

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
