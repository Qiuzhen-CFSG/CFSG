module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableSylowDiagonal

/-!
# The original central seed and marked partner in the cubic decomposable row

In the full chosen module the Sylow fixed subgroup is exactly the original
central omega subgroup. The prime-three support calculation therefore
identifies this seed as the four-element diagonal across the original
Thompson markings. Each marking together with that same seed generates
the full Thompson fixed subgroup. Once the partner is identified with the
seed centralizer, its marked centralizer is the full fixed centralizer
and is normalized by the original Sylow group, without 15.1.14.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Stellmacher Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem full_fixed_sylow_eq_seed
    (T : Sylow 2 G) {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    thompsonFixed T V ⊓ centralizer (T : Set G) = centralInvolutions T := by
  let := h.elementary
  apply le_antisymm
  · intro x hx
    have hω := (mem_omegaOneCenterAmbient_iff _ _).mp
      (h.thompsonFixed_le_omega T hM hx.1)
    exact (mem_omegaOneCenterAmbient_iff (T : Subgroup G) x).mpr
      ⟨ChapterB.thompsonJ_le _ _ hω.1,hω.2.1,hx.2⟩
  · have hZV : centralInvolutions T ≤ V := hfull ▸ le_conjugateSpanBy _ _
    exact le_inf (le_inf hZV ((centralInvolutions_le_centralizer_sylow T).trans
      (centralizer_le (ChapterB.thompsonJ_le _ _)))) (centralInvolutions_le_centralizer_sylow T)

/-- The original central omega subgroup is the four-element diagonal across
the two original Thompson markings in the full prime-three source row. -/
theorem ThompsonPair.central_seed_geometry_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V h.normalized)
      (Jhat (imageRepresentation M V h.normalized)) U)
    (d : Decomposition c.representation) (hd : d.FittingFull)
    (s : ThompsonPair (T := T) h.normalized c d)
    (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
      (c.ambientFactor d (π g k)).space)
    (hthree : s.prime = 3) :
    let A := thompsonPlane T V (c.ambientFactor d s.first).space
    let B := thompsonPlane T V (c.ambientFactor d s.second).space
    Nat.card (centralInvolutions T) = 4 ∧
      Disjoint A (centralInvolutions T) ∧ A ⊔ centralInvolutions T = thompsonFixed T V ∧
      Disjoint B (centralInvolutions T) ∧ B ⊔ centralInvolutions T = thompsonFixed T V := by
  have hfour := s.support_four_not_dvd_of_prime_three hG T hM hfull h.normalized
    c d hd π hp hs hthree s.first
  have hh := s.fixed_diagonal_of_support_four_not_dvd hM.1.2 h.normalized c d hfour
  dsimp only at hh ⊢
  rwa [full_fixed_sylow_eq_seed T hM h hfull] at hh

omit [Finite G] in
private theorem marked_centralizer_eq
    {T : Sylow 2 G} {E A Mc : Subgroup G}
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hgen : A ⊔ centralInvolutions T = E) :
    Mc ⊓ centralizer (A : Set G) = centralizer (E : Set G) := by
  subst Mc
  apply le_antisymm
  · apply le_centralizer_iff.mpr
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp inf_le_right) (le_centralizer_iff.mp inf_le_left)
  · exact le_inf (centralizer_le ((le_sup_right : centralInvolutions T ≤
      A ⊔ centralInvolutions T).trans_eq hgen))
      (centralizer_le ((le_sup_left : A ≤ A ⊔ centralInvolutions T).trans_eq hgen))

/-- The actual prime-three marked partner centralizer is normalized by the
original Sylow subgroup once the partner is its original seed centralizer. -/
theorem ThompsonPair.marked_partner_centralizer_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V h.normalized)
      (Jhat (imageRepresentation M V h.normalized)) U)
    (d : Decomposition c.representation) (hd : d.FittingFull)
    (s : ThompsonPair (T := T) h.normalized c d)
    (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
      (c.ambientFactor d (π g k)).space)
    (hthree : s.prime = 3) :
    let A := thompsonPlane T V (c.ambientFactor d s.first).space
    let B := thompsonPlane T V (c.ambientFactor d s.second).space
    Mc ⊓ centralizer (A : Set G) = centralizer (thompsonFixed T V : Set G) ∧
      Mc ⊓ centralizer (B : Set G) = centralizer (thompsonFixed T V : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((Mc ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  obtain ⟨_,_,ha,_,hb⟩ := s.central_seed_geometry_of_prime_three
    hG T hM h hfull c d hd π hp hs hthree
  have he := marked_centralizer_eq hMc ha
  refine ⟨he,marked_centralizer_eq hMc hb,?_⟩
  rw [he]
  have hTE : (T : Subgroup G) ≤ normalizer (thompsonFixed T V : Set G) :=
    le_normalizer_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans (normalizer_le_normalizer_centralizer _))
  exact hTE.trans (normalizer_le_normalizer_centralizer _)

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
