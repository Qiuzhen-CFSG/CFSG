module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison.Displacements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition.Frame

/-!
# Comparing the two actual G₂ covering centers

The A_(2n) argument recognizes a full q³ actor for any noncentral conjugate
normalizing V. Apply it backwards to a mutually normalizing pair, using the
same ambient conjugation. Its full commutator places the reciprocal center
inside V. Each of its elements is fixed by A=Vᵍ. If it were outside C_V(L),
the single-displacement theorem would express it as one commutator, forbidden
by exact fixed-vector lifting on A. Thus C_(Vᵍ)(Lᵍ) lies in C_V(L), and equal
orders give equality. Both full centers and the original actions are retained.

The Source consumer obtains mutual normalization in the nonzero-center
branch from the preceding ambient uniqueness and strict r-bound argument.
Source: Aschbacher--Smith 11.2.2(3,5), printed pp.767--768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion Atlas.G2.Explicit
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))

/-- Recognition for a whole conjugate normalizing V; Sylow placement is
unnecessary for the automizer's A_(2n) argument. -/
theorem normalizing_conjugate_actor
    (hs : @globalS G _ V D.elementary = (2*S.field.degree : ℕ))
    (g : G) (hAN : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ (u : Model S.field.Carrier)
      (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier),
      (∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
        (D.spaceEquiv (Multiplicative.ofAdd
          (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (a x) v)) : G) =
          (x : G)*(D.spaceEquiv (Multiplicative.ofAdd v) : G)*(x : G)⁻¹) ∧
      a.range = EvenTwoRank.elementary S.field.Carrier := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  have hcor : subgroupCorank A A = 0 := by simp [subgroupCorank]
  have hb : (subgroupCorank A A : ℕ∞) < globalS V := by
    rw [hcor,hs]
    exact_mod_cast (by have := S.nonbinary; omega : 0<2*S.field.degree)
  have hf := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
    (le_inf le_rfl hAN) hb hne).2
  rw [hs,ENat.toNat_natCast,hcor,Nat.sub_zero] at hf
  have hi := Parameters.RootActors.g2_original_two_family_inner D S m _
    (fixedSpaceFamily_mono (automizerRepresentation V) (by decide)
      (by have := S.nonbinary; omega : 2 ≤ 2*S.field.degree) hf)
  obtain ⟨u,hu⟩ := ActorRecognition.family_eq_conjugate_elementary S.field.card_eq
    (by have := S.nonbinary; omega) _ (ActorRecognition.original_inner_family D S m _ hi hf)
  let a₀ := RootPullback.innerActor D S m hAN hi
  have ha₀ : a₀.range = (EvenTwoRank.elementary S.field.Carrier).map (MulAut.conj u).toMonoidHom :=
    (ActorRecognition.innerActor_range D S m hAN hi).trans hu
  let a := (MulAut.conj u⁻¹).toMonoidHom.comp a₀
  refine ⟨u,a,?_,?_⟩
  · intro x v
    change (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (MulAut.conj u⁻¹ (a₀ x)) v)) : G) = _
    rw [ActorRecognition.recentered_action]
    exact RootPullback.innerActor_action D S m hAN hi x v
  · rw [MonoidHom.range_comp,ha₀,offender_map_conj_inverse]

/-- Mutual normalization supplies a full reciprocal actor and places its
covering center in the original module. -/
theorem reciprocal_full_actor
    (hs : @globalS G _ V D.elementary = (2*S.field.degree : ℕ))
    (g : G) (hAN : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hVA : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ (u : Model S.field.Carrier) (b : V →* Model S.field.Carrier),
      (∀ (x : V) (v : D.space),
        MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd
          (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (b x) v)) : G) =
          (x : G)*MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd v) : G)*(x : G)⁻¹) ∧
      (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ≤ V := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := V.map (MulAut.conj g⁻¹).toMonoidHom
  have hBN : B ≤ normalizer (V : Set G) := by
    have hh := map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hVA
    rwa [map_equiv_normalizer_eq,offender_map_conj_inverse] at hh
  have hnon : ⁅V,B⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) hz
    rw [map_commutator,offender_map_conj_map, mul_inv_cancel,
      show (MulAut.conj (1:G)).toMonoidHom=MonoidHom.id G from by ext x; simp,
      map_id,Subgroup.map_bot,commutator_comm] at hh
    exact hne hh
  obtain ⟨u,b,hb,hbr⟩ := normalizing_conjugate_actor D S m hs g⁻¹ hBN hnon
  let e := MulAut.conj g⁻¹
  let b' := b.comp (e.subgroupMap V).toMonoidHom
  refine ⟨u,b',?_,?_⟩
  · intro x v
    have hh := congrArg (MulAut.conj g) (hb (e.subgroupMap V x) v)
    change MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd
        (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (b' x) v)) : G) =
      MulAut.conj g ((e x : G)*(D.spaceEquiv (Multiplicative.ofAdd v) : G)*(e x : G)⁻¹) at hh
    simpa only [map_mul,map_inv,show ∀ y : G, MulAut.conj g (e y)=y from
      fun y => by simp [e,MulAut.conj_apply,mul_assoc]] using hh
  · have hc := CentralContainment.central_le_full_commutator D S
      (ActorRecognition.recentered D S m u) B b hb hbr
    have hh := map_mono (f:=(MulAut.conj g).toMonoidHom) hc
    rw [map_commutator,offender_map_conj_map,mul_inv_cancel,
      show (MulAut.conj (1:G)).toMonoidHom=MonoidHom.id G from by ext x; simp,map_id] at hh
    exact hh.trans (le_normalizer_iff_commutator_le_right.mp hAN)

/-- The two full covering centers agree, derived from their single-commutator
characterization rather than from augmented-plane equalities. -/
theorem covering_centers_eq
    (hs : @globalS G _ V D.elementary = (2*S.field.degree : ℕ))
    (g : G) (hAN : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hVA : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hact : ∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G)*(D.spaceEquiv (Multiplicative.ofAdd v) : G)*(x : G)⁻¹)
    (ha : a.range=EvenTwoRank.elementary S.field.Carrier) :
    (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      V ⊓ centralizer (L : Set G) := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  obtain ⟨u,b,hb,hcV⟩ := reciprocal_full_actor D S m hs g hAN hVA hne
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj g).injective])
  intro x hx
  by_contra hn
  have hxA : x ∈ A := map_mono (show V ⊓ centralizer (L : Set G) ≤ V from inf_le_left) hx
  have hxC : x ∈ centralizer (A : Set G) := Subgroup.le_centralizer A hxA
  obtain ⟨z,hz,y,hy,he⟩ := fixed_noncentral_is_commutator D S m A a hact ha x ⟨hcV hx,hxC⟩ hn
  have hc : ⁅y,z⁆ ∈ (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [←commutatorElement_inv,he]
    exact Subgroup.inv_mem _ hx
  have h1 := reciprocal_central_commutator_eq_one D S (ActorRecognition.recentered D S m u)
    g V b hb ⟨y,hy⟩ z hz hc
  have hx1 : x=1 := by
    rw [←he,←commutatorElement_inv,h1,inv_one]
  exact hn (hx1.symm ▸ Subgroup.one_mem _)


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CenterComparison
