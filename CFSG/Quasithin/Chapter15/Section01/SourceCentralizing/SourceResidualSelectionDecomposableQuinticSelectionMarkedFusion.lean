module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSylow
public import Theory.GroupTheory.WeakClosureQuotientFusion
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSylow

/-!
# The actual marked centralizer in the order-four partner branch

The partner module U is a full diagonal between the original two marked
planes. For g in Mc fixing the first plane, pointwise Thompson correction
inside C_G(Z1) intersect C_G(U) realizes its action on U by an element of
M that still fixes Z1 and normalizes U. The original support permutation
and diagonal geometry force this element to fix E pointwise. Thus g fixes
U, and the marked partner centralizer is exactly C_G(E), hence T-invariant.

The deliberate same-package internal import reuses the diagonal-complement
proof from the frozen Sylow implementation. It enters no public statement.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem PreparedChosenModule.marked_normalizer_pointwise_correction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V U Z : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G)≤centralizer (localModule T M:Set G))
    (h : PreparedChosenModule T M V) (hUV : U≤V) (hZV : Z≤V)
    (g : G) (hgZ : g∈centralizer (Z:Set G)) (hgU : g∈normalizer (U:Set G)) :
    ∃n∈M⊓centralizer (Z:Set G), n∈normalizer (U:Set G) ∧
      ∀u∈U, n*u*n⁻¹=g*u*g⁻¹ := by
  let J := elementaryAbelianMaxJ (T:Subgroup G)
  let K := centralizer (Z:Set G)⊓centralizer (U:Set G)
  have hJV : J≤centralizer (V:Set G) := hJ.trans (centralizer_le h.le_local)
  have hJK : J≤K := le_inf (hJV.trans (centralizer_le hZV))
    (hJV.trans (centralizer_le hUV))
  have hgK : J.map (MulAut.conj g).toMonoidHom≤K := by
    apply le_inf
    · exact (map_mono (hJV.trans (centralizer_le hZV))).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp ((centralizer (Z:Set G)).le_normalizer hgZ))
    · exact (map_mono (hJV.trans (centralizer_le hUV))).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp ((normalizer_le_normalizer_centralizer U) hgU))
  obtain ⟨k,hk⟩ := Sylow.WeakClosure.normalizer_correction T J
    (sSup_le fun _ hA=>hA.1) (maxJ_weakly_closed_normalizer T) K hJK g hgK
  refine ⟨(k:G)*g,⟨(source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hk,
    (centralizer (Z:Set G)).mul_mem k.property.1 hgZ⟩,
    (normalizer (U:Set G)).mul_mem ((Subgroup.centralizer_le_normalizer (U:Set G)) k.property.2) hgU,?_⟩
  intro u hu
  have hgu : g*u*g⁻¹∈U := (mem_normalizer_iff.mp hgU u).mp hu
  calc
    _=(k:G)*(g*u*g⁻¹)*(k:G)⁻¹ := by group
    _=g*u*g⁻¹ := by rw [←k.property.2 _ hgu,mul_inv_cancel_right]

/-- The original order-four partner branch has marked centralizer C_G(E),
without a global residual assumption or a prime-residual marker premise. -/
theorem PreparedChosenModule.decomposable_five_partner_four_marked_centralizer
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
      Nat.card (localModule T Mc)=4 →
      let E := thompsonFixed T V
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      centralizer (Z₁:Set G)⊓Mc=centralizer (E:Set G) ∧
      (T:Subgroup G)≤normalizer (centralizer (Z₁:Set G)⊓Mc : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let W := localModule T Mc
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨hEN,hIE,hWE⟩ := h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,hd₂,hjoin₁,_,_⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz=>(centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let : IsElementaryAbelian 2 W := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hMcC.1.1,hTMc⟩
  have hWN : Mc≤normalizer (W:Set G) := le_normalizer_conjugateSpanBy _ _
  have hNW : normalizer (W:Set G)≤Mc := hMcC.1.2
    ⟨W,(one_lt_card_iff_ne_bot W).mp (by change 1<Nat.card (localModule T Mc); omega),
      IsElementaryAbelian.isPGroup 2 W,rfl⟩ hWN
  have hTE : (T:Subgroup G)≤normalizer (E:Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hZne : Z₁≠Z₂ := by
    intro he
    have hb : Z₁=⊥ := by
      have hh := s.thompson_disjoint
      change Z₁⊓Z₂=⊥ at hh
      simpa only [←he,inf_idem] using hh
    have hc := s.thompson_card s.first
    change Nat.card Z₁=4 at hc
    rw [hb,card_bot] at hc
    omega
  have hMC : M⊓Mc⊓centralizer (Z₁:Set G)≤centralizer (E:Set G) := by
    intro n hn
    let x : M := ⟨n,hn.1.1⟩
    let a : internalActionImage M V h.normalized := (actionHom M V h.normalized).rangeRestrict x
    have hnmap : E.map (MulAut.conj n).toMonoidHom=E :=
      mem_normalizer_iff_map_conj_eq.mp (hIE hn.1)
    have hmap (i : d.Index) :
        (thompsonPlane T V (c.ambientFactor d i).space).map (MulAut.conj n).toMonoidHom=
        thompsonPlane T V (c.ambientFactor d (π a i)).space := by
      change ((plane _ _)⊓E).map _=(plane _ _)⊓E
      rw [map_inf _ _ _ (MulAut.conj n).injective,
        hnmap,plane_conjugate h.normalized _ x]
      exact congrArg (fun P=>plane V P⊓E) (hs a i)
    have hfix : Z₁.map (MulAut.conj n).toMonoidHom=Z₁ :=
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer (Z₁:Set G)) hn.2)
    have hi : π a s.first=s.first := by
      rcases s.covers (π a s.first) with hh|hh
      · exact hh
      · have he := hmap s.first
        rw [hh] at he
        exact (hZne (hfix.symm.trans he)).elim
    have hj : π a s.second=s.second := by
      rcases s.covers (π a s.second) with hh|hh
      · have he : s.second=s.first := (π a).injective (hh.trans hi.symm)
        exact (s.distinct he.symm).elim
      · exact hh
    have hn₂ : n∈normalizer (Z₂:Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change Z₂.map (MulAut.conj n).toMonoidHom=Z₂
      have hh:=hmap s.second
      change Z₂.map (MulAut.conj n).toMonoidHom=thompsonPlane T V (c.ambientFactor d (π a s.second)).space at hh
      rw [hj] at hh
      exact hh
    exact centralizes_diagonal_complement E Z₁ Z₂ W inf_le_right inf_le_right hWE
      s.thompson_split.symm hjoin₁ hd₂ n (hIE hn.1) (hWN hn.1.2) hn₂ hn.2
  have he : centralizer (Z₁:Set G)⊓Mc=centralizer (E:Set G) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨n,hn,hnW,hnact⟩ := h.marked_normalizer_pointwise_correction hG T hM hJ
        (hWE.trans inf_le_left) (show Z₁≤V from inf_le_right.trans inf_le_left)
        g hg.1 (hWN hg.2)
      have hnE : n∈centralizer (E:Set G) := hMC ⟨⟨hn.1,hNW hnW⟩,hn.2⟩
      have hgW : g∈centralizer (W:Set G) := by
        intro w hw
        have hh : g*w*g⁻¹=w := by
          rw [←hnact w hw,←hnE w (hWE hw),mul_inv_cancel_right]
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      have hcent : W⊔Z₁≤centralizer ({g}:Set G) := sup_le
        (by intro w hw; exact mem_centralizer_singleton_iff.mpr (hgW w hw))
        (by intro z hz; exact mem_centralizer_singleton_iff.mpr (hg.1 z hz))
      intro e he
      exact mem_centralizer_singleton_iff.mp (hcent (hjoin₁.symm ▸ he))
    · exact le_inf (centralizer_le (show Z₁≤E from inf_le_right))
        ((Subgroup.centralizer_le_normalizer (E:Set G)).trans hEN)
  refine ⟨he,?_⟩
  change (T:Subgroup G)≤normalizer ((centralizer (Z₁:Set G)⊓Mc : Subgroup G):Set G)
  rw [he]
  exact hTE.trans (normalizer_le_normalizer_centralizer _)

end CFSG.Quasithin.Chapter15.Section01
