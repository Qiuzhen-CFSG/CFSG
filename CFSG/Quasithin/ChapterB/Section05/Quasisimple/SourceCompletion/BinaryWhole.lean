module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.MovedInduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.OuterActorElimination

/-!
# Binary reducible source actions have G=L

A binary-natural L-submodule has its complete general linear group already
realized by L. An ambient stabilizer therefore differs from an element of L
by an element centralizing L. Since F*=L and Z(L)=1, that difference is trivial.
Thus an element outside L moves this simple submodule to a disjoint translate.

The existing outer-involution rank calculation and offender inequality exclude
such an outer offender. Offender generation gives G=L. The actual source
consumer constructs the required natural submodule as the first term of the
purified chief flag on [V,L], so no socle decomposition, disjointness, or marked
conjugation action is assumed by the caller.

Source: Aschbacher--Smith B.5.1, printed pp.101--102, the G=L argument in
case (II) and the binary natural-module branch. The proof uses the source's
outer-offender estimate and the full binary natural linear action.
-/

public section

open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A binary-natural submodule has no outer stabilizer: its full linear
automorphism group is already the original component image. -/
theorem binary_natural_stabilizer_le (L : Subgroup G) [L.Normal]
    (hc : centralizer (L : Set G) = ⊥)
    (I : Subrepresentation (ρ.comp L.subtype)) {d : ℕ}
    (hn : IsLinearNatural I.toRepresentation BinaryField.two d) :
    subspaceStabilizer ρ I.toSubmodule ≤ L := by
  obtain ⟨e⟩ := hn
  change ActionEquiv I.toRepresentation (specialLinearNatural (k := ZMod 2) d) at e
  have hf : Function.Injective I.toRepresentation := by
    intro x y hxy
    apply e.groupEquiv.injective
    apply (BinaryLinear.OuterCyclic.slEquivLinear d).injective
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
    change (specialLinearNatural (k := ZMod 2) d) (e.groupEquiv x) (e.linearEquiv v) =
      (specialLinearNatural (k := ZMod 2) d) (e.groupEquiv y) (e.linearEquiv v)
    rw [← e.intertwines,← e.intertwines]
    exact congrArg e.linearEquiv (LinearMap.congr_fun hxy v)
  intro b hb
  let B := LinearMap.GeneralLinearGroup.toLinearEquiv
    ((stabilizerRepresentation ρ I.toSubmodule).asGroupHom ⟨b,hb⟩)
  let t := (e.linearEquiv.symm.trans B).trans e.linearEquiv
  let l : L := e.groupEquiv.symm ((BinaryLinear.OuterCyclic.slEquivLinear d).symm t)
  have hl (v : I.toSubmodule) : ρ l.val v.val = ρ b v.val := by
    have hh := e.intertwines l v
    rw [show e.groupEquiv l = (BinaryLinear.OuterCyclic.slEquivLinear d).symm t from
      e.groupEquiv.apply_symm_apply _] at hh
    have ht : (specialLinearNatural (k := ZMod 2) d)
        ((BinaryLinear.OuterCyclic.slEquivLinear d).symm t) (e.linearEquiv v) =
        t (e.linearEquiv v) := by
      have he := congrArg (fun f : BinaryLinear.OuterCyclic.LinearGroup d => f (e.linearEquiv v))
        ((BinaryLinear.OuterCyclic.slEquivLinear d).apply_symm_apply t)
      exact he
    rw [ht] at hh
    have he : I.toRepresentation l v = B v := e.linearEquiv.injective (by
      simpa only [t,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using hh)
    exact congrArg (fun v : I.toSubmodule => (v : V)) he
  let c : G := l.val⁻¹ * b
  have hcI (v : I.toSubmodule) : ρ c v.val = v.val := by
    change ρ (l.val⁻¹*b) v.val = v.val
    rw [map_mul,Module.End.mul_apply,← hl v,← Module.End.mul_apply,← map_mul,inv_mul_cancel,
      map_one,Module.End.one_apply]
  have hci (v : I.toSubmodule) : ρ c⁻¹ v.val = v.val := by
    have he := congrArg (ρ c⁻¹) (hcI v)
    simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using he.symm
  have hcent : c ∈ centralizer (L : Set G) := by
    intro x hx
    let x' : L := ⟨x,hx⟩
    have hconj : (⟨c*x*c⁻¹,(inferInstance : L.Normal).conj_mem x hx c⟩ : L) = x' := by
      apply hf
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change ρ (c*x*c⁻¹) v.val = ρ x v.val
      rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hci v]
      exact hcI (I.toRepresentation x' v)
    have he := congrArg Subtype.val hconj
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have he : c = 1 := by
    rw [hc] at hcent
    exact hcent
  have hb' : b = l.val := by
    exact (inv_mul_eq_one.mp he).symm
  exact hb' ▸ l.property

/-- With F*=L, a single genuine binary-natural submodule already excludes
all outer offenders. The disjoint translate condition is proved from natural
module recognition, not assumed as a socle decomposition. -/
theorem whole_of_binary_natural_submodule (L : Subgroup G) [L.Normal]
    (hfit : generalizedFitting G = L)
    (I : Subrepresentation (ρ.comp L.subtype)) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hn : IsLinearNatural I.toRepresentation BinaryField.two d)
    (hgen : offenderSubgroup ρ = ⊤) : L = ⊤ := by
  obtain ⟨e⟩ := hn
  change ActionEquiv I.toRepresentation (specialLinearNatural (k := ZMod 2) d) at e
  have hz : center L = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr e.groupEquiv).toEquiv]
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega : 0 < d)]
    exact Subgroup.card_bot
  have hc : centralizer (L : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxL : x ∈ L := by
      rw [← hfit]
      exact QuasisimpleSections.centralizer_generalizedFitting_le (hfit.symm ▸ hx)
    have hxc : (⟨x,hxL⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (hx l l.property)
    have he : (⟨x,hxL⟩ : L) = 1 := by
      rw [hz] at hxc
      exact hxc
    exact congrArg Subtype.val he
  let mark := e.groupEquiv.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d)).symm
  let φ : G →* MulAut PSL(d,ZMod 2) :=
    (MulAut.congr mark).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut L)
  have hφ : Function.Injective φ := (MulAut.congr mark).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L hc)
  have hmark : L.map φ = MulAut.innerSubgroup PSL(d,ZMod 2) := by
    rw [show φ = (MulAut.congr mark).toMonoidHom.comp
      (MulAut.conjNormal : G →* MulAut L) from rfl,← Subgroup.map_map]
    have hL : L.map (MulAut.conjNormal : G →* MulAut L) = MulAut.innerSubgroup L := by
      ext a
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,hx⟩,MulAut.conjNormal_val.symm⟩
      · rintro ⟨x,rfl⟩
        exact ⟨x,x.property,MulAut.conjNormal_val⟩
    rw [hL,MulAut.map_innerSubgroup_congr]
  have hdim : d ≤ Module.finrank (ZMod 2) I.toSubmodule := by
    rw [e.linearEquiv.finrank_eq]
    change d ≤ Module.finrank (ZMod 2) (Fin d → ZMod 2)
    simp only [Module.finrank_fin_fun]
    exact le_rfl
  have hI : IsAtom I := (Subrepresentation.irreducible_iff_isAtom _).mp
    (ExtensionConsequences.irreducible_of_equiv e
      (ExtensionConsequences.linearNatural_irreducible BinaryField.two (by omega)))
  have hstab := binary_natural_stabilizer_le ρ L hc I ⟨e⟩
  apply whole_of_marked_outer_summands ρ hd φ hφ L hmark I.toSubmodule hdim
  · apply le_subspaceStabilizer
    intro g hg v hv
    exact I.apply_mem_toSubmodule ⟨g,hg⟩ hv
  · intro g hg hfix
    apply hφ
    have hcent : g ∈ centralizer (L : Set G) := by
      intro x hx
      -- A pointwise-fixed natural action is faithful on L.
      have hg1 : e.groupEquiv ⟨g,hg⟩ = 1 := by
        apply (BinaryLinear.OuterCyclic.slEquivLinear d).injective
        rw [map_one]
        apply LinearEquiv.ext
        intro w
        obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
        change (specialLinearNatural (k := ZMod 2) d) (e.groupEquiv ⟨g,hg⟩) (e.linearEquiv v) = e.linearEquiv v
        rw [← e.intertwines]
        exact congrArg e.linearEquiv (Subtype.ext (hfix v v.property))
      have hg1' : g = 1 := congrArg Subtype.val (e.groupEquiv.injective (hg1.trans e.groupEquiv.map_one.symm))
      simp only [hg1',mul_one,one_mul]
    have hg1 : g = 1 := by
      rw [hc] at hcent
      exact hcent
    exact congrArg φ hg1
  · intro b hb
    let J := conjugateSubrepresentationOrderIso ρ L b I
    have hJ : IsAtom J := ((conjugateSubrepresentationOrderIso ρ L b).isAtom_iff I).mpr hI
    have hne : I ≠ J := by
      intro he
      apply hb
      apply hstab
      have he' : I.toSubmodule.map (ρ b) = I.toSubmodule := by
        rw [← conjugateSubrepresentationOrderIso_toSubmodule]
        exact congrArg Subrepresentation.toSubmodule he.symm
      have hm := (subspace_map_eq_iff ρ I.toSubmodule b).mp he'
      exact hm
    have hd := hI.disjoint_of_ne hJ hne
    apply Submodule.disjoint_def.mpr
    intro v hvI hvJ
    have hv : v ∈ I ⊓ J := ⟨hvI,by
      rw [show J.toSubmodule = I.toSubmodule.map (ρ b) from
        conjugateSubrepresentationOrderIso_toSubmodule ρ L b I]
      exact hvJ⟩
    rw [hd.eq_bot] at hv
    exact hv
  · exact hgen

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Remove the zero denominator of the first literal chief section. -/
theorem first_chief_natural (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    {d : ℕ}
    (hn : IsLinearNatural ((sectionRepresentation ρ (f.chain 0) (f.chain 1)).comp C.subtype)
      BinaryField.two d) :
    IsLinearNatural ((f.chain 1).toRepresentation.comp C.subtype) BinaryField.two d := by
  obtain ⟨e⟩ := hn
  have hz : (sectionLower ρ (f.chain 0) (f.chain 1)).toSubmodule = ⊥ := by
    rw [f.bottom]
    change (⊥ : Submodule (ZMod 2) V).comap (f.chain 1).toSubmodule.subtype = ⊥
    rw [Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr (f.chain 1).toSubmodule.subtype_injective
  let q := (sectionLower ρ (f.chain 0) (f.chain 1)).toSubmodule.quotEquivOfEqBot hz
  exact ⟨{ groupEquiv := e.groupEquiv
           linearEquiv := q.symm.trans e.linearEquiv
           intertwines := fun g v => e.intertwines g (q.symm v) }⟩

/-- The genuine reducible binary B.5.1 source action has no outer extension:
G=L. The first natural submodule is constructed from the actual moved chief
flag; no socle or disjointness hypothesis is supplied by the caller. -/
theorem binary_reducible_whole
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : L ≃* SL(d,ZMod 2)) : L = ⊤ := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  have hfit := binary_source_fitting ρ h hd mark
  obtain ⟨s,A,hA,f,hindices,hn,_⟩ := binary_moved_pure_flag ρ hK earlier h hnot hd mark
  let μ := s.space.toRepresentation
  have hμ := moved_source_hypothesis ρ h s hfit
  let H := L ⊔ A
  let σ := μ.comp H.subtype
  have hlen : 0 < f.length := by
    have hm := f.multiple
    rw [hindices,Finset.card_range] at hm
    omega
  have hnfirst := first_chief_natural σ (generalizedFitting H) f (hn 0 hlen).2.2
  let I : Subrepresentation (μ.comp L.subtype) := {
    toSubmodule := (f.chain 1).toSubmodule
    apply_mem_toSubmodule l _ hv :=
      (f.chain 1).apply_mem_toSubmodule ⟨l.val,(show L ≤ H from le_sup_left) l.property⟩ hv }
  have hs : L ⊔ A ≤ subspaceStabilizer μ I.toSubmodule := by
    apply le_subspaceStabilizer
    intro g hg v hv
    exact (f.chain 1).apply_mem_toSubmodule ⟨g,hg⟩ hv
  have hnatural : IsLinearNatural I.toRepresentation BinaryField.two d :=
    natural_on_component μ L hfit h.twoCore hA.1 I hs hnfirst
  exact whole_of_binary_natural_submodule μ L hfit I hd hnatural hμ.generated

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
