module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSectionKernel
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionDisplacement

/-!
# The original quintic seed normalizer fixes its diagonal quotient

Thompson weak closure corrects an element normalizing E and centralizing Uc
by an element of C_G(E) into the original M. Its action permutes the two
marked planes and fixes their full diagonal Uc, so its displacement on E
lies in Uc. The private diagonal calculation is intentionally reused from
the frozen displacement implementation in this same source subsystem.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The actual ambient seed normalizer centralizing the order-four partner
module fixes the literal marked quotient E/Uc pointwise. -/
theorem PreparedChosenModule.decomposable_five_partner_four_seed_normalizer_displacement
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
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      ⁅normalizer (E:Set G) ⊓ centralizer (Uc:Set G), E⁆ ≤ Uc := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let J := elementaryAbelianMaxJ (T:Subgroup G)
  let K := centralizer (E:Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨hEN,hIE,hUE⟩ := h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,_,hjoin₁,hjoin₂,_⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hJK : J≤K := (hJ.trans (centralizer_le h.le_local)).trans
    (centralizer_le (show E≤V from inf_le_left))
  have hKMc : K≤Mc := (Subgroup.centralizer_le_normalizer (E:Set G)).trans hEN
  apply commutator_le.mpr
  intro g hg e he
  have hgMc : g∈Mc := hEN hg.1
  have hgJK : J.map (MulAut.conj g).toMonoidHom≤K :=
    (map_mono hJK).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((normalizer_le_normalizer_centralizer E) hg.1))
  obtain ⟨k,hk⟩ := Sylow.WeakClosure.normalizer_correction T J
    (sSup_le fun _ hA=>hA.1) (maxJ_weakly_closed_normalizer T) K hJK g hgJK
  let n := (k:G)*g
  have hnM : n∈M := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hk
  have hnMc : n∈Mc := Mc.mul_mem (hKMc k.property) hgMc
  have hnE : n∈normalizer (E:Set G) := hIE ⟨hnM,hnMc⟩
  have hnC : n∈centralizer (Uc:Set G) :=
    (centralizer (Uc:Set G)).mul_mem ((centralizer_le hUE) k.property) hg.2
  have hact (x:G) (hx:x∈E) : n*x*n⁻¹=g*x*g⁻¹ := by
    have hgx : g*x*g⁻¹∈E := (mem_normalizer_iff.mp hg.1 x).mp hx
    calc
      _=(k:G)*(g*x*g⁻¹)*(k:G)⁻¹ := by dsimp [n]; group
      _=g*x*g⁻¹ := by rw [←k.property _ hgx,mul_inv_cancel_right]
  let a : internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict ⟨n,hnM⟩
  have hnmap : E.map (MulAut.conj n).toMonoidHom=E :=
    mem_normalizer_iff_map_conj_eq.mp hnE
  have hmap (i:d.Index) :
      (thompsonPlane T V (c.ambientFactor d i).space).map (MulAut.conj n).toMonoidHom=
      thompsonPlane T V (c.ambientFactor d (π a i)).space := by
    change ((plane _ _)⊓E).map _=(plane _ _)⊓E
    rw [map_inf _ _ _ (MulAut.conj n).injective,
      hnmap,plane_conjugate h.normalized _ ⟨n,hnM⟩]
    exact congrArg (fun P=>plane V P⊓E) (hs a i)
  have hpermi : (π a s.first=s.first ∧ π a s.second=s.second) ∨
      (π a s.first=s.second ∧ π a s.second=s.first) := by
    rcases s.covers (π a s.first) with hi|hi
    · left
      refine ⟨hi,?_⟩
      rcases s.covers (π a s.second) with hj|hj
      · exact (s.distinct ((π a).injective (hi.trans hj.symm))).elim
      · exact hj
    · right
      refine ⟨hi,?_⟩
      rcases s.covers (π a s.second) with hj|hj
      · exact hj
      · exact (s.distinct ((π a).injective (hi.trans hj.symm))).elim
  have hpZ : (Z₁.map (MulAut.conj n).toMonoidHom=Z₁ ∧
      Z₂.map (MulAut.conj n).toMonoidHom=Z₂) ∨
      (Z₁.map (MulAut.conj n).toMonoidHom=Z₂ ∧
      Z₂.map (MulAut.conj n).toMonoidHom=Z₁) := by
    rcases hpermi with hp|hp
    · exact Or.inl ⟨by simpa only [hp.1] using hmap s.first,
        by simpa only [hp.2] using hmap s.second⟩
    · exact Or.inr ⟨by simpa only [hp.1] using hmap s.first,
        by simpa only [hp.2] using hmap s.second⟩
  have hh := ambient_diagonal_displacement E Z₁ Z₂ Uc inf_le_right inf_le_right hUE
    (disjoint_iff.mpr s.thompson_disjoint) hjoin₁ hjoin₂ n hnE hnC hpZ e he
  change (n*e*n⁻¹)*e⁻¹∈Uc at hh
  rw [hact e he] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section01
