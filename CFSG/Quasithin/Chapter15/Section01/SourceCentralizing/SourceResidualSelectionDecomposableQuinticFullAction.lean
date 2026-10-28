module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticFixedAction
public import Theory.GroupAction.FourPerfectImage

/-!
# The ternary residual of the full Thompson action

When the actual third local has the whole original Thompson fixed subgroup
as its module, ordering transfers its action from the original intersection.
The two-residual of that intersection fixes the two support indices. Its
action on each Thompson four-group has order dividing three, so its cube
centralizes their join. This proves the assertion for the literal third-local
action, without recognizing that action or replacing the source residual.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem cube_centralizes_four_of_twoPerfect
    (B Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hB : IsPPerfect 2 B) (hc : Nat.card Z = 4)
    (hn : B ≤ normalizer (Z : Set G)) :
    ∀ b ∈ B, b^3 ∈ centralizer (Z : Set G) := by
  let f := actionHom B Z hn
  have hd := MulAut.card_range_dvd_three_of_twoPerfect hB hc f
  intro b hb
  have he : (f.rangeRestrict ⟨b,hb⟩)^3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard _).trans hd)
  have hk : (⟨b,hb⟩ : B)^3 ∈ f.ker := by
    change f ((⟨b,hb⟩ : B)^3) = 1
    rw [map_pow]
    exact congrArg Subtype.val he
  rw [actionHom_ker] at hk
  exact hk

/-- The literal third-local action has ternary two-residual when its module
is the original full Thompson fixed subgroup. No prime-row restriction or
previous residual-normalization hypothesis is needed. -/
theorem PreparedChosenModule.decomposable_full_thompson_action_residual_threeGroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (_s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      N ∈ maximalTwoLocalOvergroups (T : Subgroup G) →
      localModule T N = thompsonFixed T V →
      IsPGroup 3 (pResidual 2 (internalActionImage N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N))) := by
  subst V
  let := h.elementary
  intro U c d s π hs hdec hN hE
  let E := thompsonFixed T (localModule T M)
  let H := M⊓N
  let B := (pResidual 2 H).map H.subtype
  let f := (actionHom M (localModule T M) h.normalized).rangeRestrict
  let i : B →* M := B.subtype.codRestrict M (fun b =>
    (show B ≤ H from map_subtype_le _) b.property |>.1)
  have hB : IsPPerfect 2 B := isPPerfect_embedded_pResidual 2 H
  have hperm : IsPGroup 2 (Equiv.Perm d.Index) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_perm,hdec.1]
    decide
  have hπ : ∀ b : B, π (f (i b)) = 1 := by
    intro b
    exact DFunLike.congr_fun
      (hB.hom_eq_one_of_isPGroup hperm (π.comp (f.comp i))) b
  have hBE : B ≤ normalizer (E : Set G) := by
    change B ≤ normalizer (thompsonFixed T (localModule T M) : Set G)
    rw [←hE]
    exact (map_subtype_le _).trans
      (inf_le_right.trans (le_normalizer_conjugateSpanBy (centralInvolutions T) N))
  have hBZ (k : d.Index) : B ≤ normalizer
      (thompsonPlane T (localModule T M) (c.ambientFactor d k).space : Set G) := by
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := mem_normalizer_iff_map_conj_eq.mp (hBE hb)
    change ((plane _ _)⊓E).map _ = (plane _ _)⊓E
    rw [map_inf _ _ _ (MulAut.conj b).injective,he]
    have hp := plane_conjugate h.normalized (c.ambientFactor d k).space (i ⟨b,hb⟩)
    change (plane (localModule T M) (c.ambientFactor d k).space).map
      (MulAut.conj b).toMonoidHom = _ at hp
    apply (congrArg (fun P : Subgroup G => P ⊓ E) hp).trans
    apply congrArg (fun P => plane (localModule T M) P ⊓ E)
    simpa only [hπ ⟨b,hb⟩,Equiv.Perm.one_apply] using hs (f (i ⟨b,hb⟩)) k
  have hcube : ∀ b∈B, b^3 ∈ centralizer (E : Set G) := by
    intro b hb
    have hz (k : d.Index) : b^3 ∈ centralizer
        (thompsonPlane T (localModule T M) (c.ambientFactor d k).space : Set G) := by
      let : IsElementaryAbelian 2
          (thompsonPlane T (localModule T M) (c.ambientFactor d k).space) :=
        IsElementaryAbelian.of_le (inf_le_right.trans inf_le_left)
      exact cube_centralizes_four_of_twoPerfect B _ hB (s.thompson_card k) (hBZ k) b hb
    have h₁ := zpowers_le.mpr (hz s.first)
    have h₂ := zpowers_le.mpr (hz s.second)
    have hh := le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp h₁)
      (le_centralizer_iff.mp h₂))
    rw [←s.thompson_split] at hh
    exact hh (mem_zpowers _)
  let W := localModule T N
  let hn : N ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy (centralInvolutions T) N
  let g := (actionHom N W hn).rangeRestrict
  let j : H →* N := H.subtype.codRestrict N (fun x => x.property.2)
  let k := g.comp j
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hk : Function.Surjective k := by
    intro a
    obtain ⟨n,hn⟩ := (actionHom N W hn).rangeRestrict_surjective a
    obtain ⟨x,hx,y,hy,he⟩ := hord n n.property
    have hy1 : g ⟨y,hy.1⟩ = 1 := by
      apply Subtype.ext
      exact (show (⟨y,hy.1⟩ : N) ∈ (actionHom N W _).ker from
        (actionHom_ker N W _).symm ▸ hy.2)
    have hnprod : n = (⟨x,hx.1⟩ : N) * ⟨y,hy.1⟩ := Subtype.ext he.symm
    refine ⟨⟨x,⟨hx.2,hx.1⟩⟩,?_⟩
    change g n = a at hn
    rw [hnprod,map_mul,hy1,mul_one] at hn
    exact hn
  have hres := map_pResidual_of_surjective 2 k hk
  intro a
  have ha : (a : internalActionImage N W hn) ∈ (pResidual 2 H).map k :=
    hres.symm ▸ a.property
  obtain ⟨b,hb,hba⟩ := ha
  have hpow : k (b^3) = 1 := by
    apply Subtype.ext
    have hc : (b : G)^3 ∈ centralizer (W : Set G) := by
      change (b : G)^3 ∈ centralizer (localModule T N : Set G)
      rw [hE]
      exact hcube b (mem_map_of_mem H.subtype hb)
    exact (show j (b^3) ∈ (actionHom N W hn).ker from (actionHom_ker N W hn).symm ▸ hc)
  have he : (k b)^3 = 1 := (k.map_pow b 3).symm.trans hpow
  exact ⟨1,Subtype.ext ((congrArg (fun z => z^3) hba).symm.trans he)⟩

end CFSG.Quasithin.Chapter15.Section01
