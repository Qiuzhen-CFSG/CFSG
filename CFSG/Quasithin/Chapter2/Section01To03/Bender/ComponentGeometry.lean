module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FusionLocalControl
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The maximal-component intersection argument in the Bender reduction

Choose a maximal ordinary component among the bad centralizers. The
containment output of I.3.2 identifies it as a component of every centralizer
of a nonidentity vector in C_U(L). Distinct conjugates with intersecting
fixed subgroups therefore commute.

The source split U = C_U(L)(U ∩ L) then makes the two fixed subgroups
generate U. Their order formula shows |C_U(L)|² > |U|, so all conjugate
fixed subgroups intersect. Three distinct components would give an odd
rank-three subgroup in an actual two-local. The remaining orbit has at most
two members; its nontrivial intersection is M-invariant, contradicting
irreducibility. Thus intersection identifies the component itself, which
is stronger than TI of the fixed subgroups.

Source: Aschbacher–Smith, Proposition 2.2.2, printed p.520 (PDF p.537).
The projected-factor split, the I.3.2 containment, and the two-local rank
witnesses remain explicit source inputs. This module proves their geometric
consequence; it does not assert Bender recognition.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- Left conjugation by an element of M. The source right-conjugation
convention is obtained by replacing that element by its inverse. -/
abbrev componentConjugate (L : Subgroup G) (m : M) : Subgroup G :=
  L.map (MulAut.conj (m : G)).toMonoidHom

/-- The actual subgroup C_U(L), retained in the ambient G. -/
abbrev componentFixedSubgroup (w : LocalControlWitness T M) (L : Subgroup G) :
    Subgroup G := w.U ⊓ centralizer (L : Set G)

omit [Finite G] in
/-- Identity conjugation fixes every subgroup. -/
theorem componentConjugate_one (A : Subgroup G) : componentConjugate A (1 : M) = A := by
  have he : (MulAut.conj ((1 : M) : G)).toMonoidHom = MonoidHom.id G := by
    ext a
    simp
  exact (congrArg (fun f => A.map f) he).trans A.map_id

omit [Finite G] in
private theorem map_centralizer_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

omit [Finite G] in
theorem componentFixedSubgroup_conjugate (w : LocalControlWitness T M)
    (L : Subgroup G) (m : M) :
    componentFixedSubgroup w (componentConjugate L m) =
      componentConjugate (componentFixedSubgroup w L) m := by
  have hu : componentConjugate w.U m = w.U :=
    mem_normalizer_iff_map_conj_eq.mp (w.normalizes m.property)
  unfold componentFixedSubgroup componentConjugate at *
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (m : G)).injective,
    map_centralizer_equiv, hu]

omit [Finite G] in
theorem componentFixedSubgroup_ne_self (w : LocalControlWitness T M)
    (L : Subgroup G) (hLM : ¬ L ≤ M) : componentFixedSubgroup w L ≠ w.U := by
  intro he
  apply hLM
  rw [← w.normalizer_eq]
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  apply le_centralizer_iff.mp
  exact he ▸ (inf_le_right : componentFixedSubgroup w L ≤ centralizer (L : Set G))

omit [Finite G] in
private theorem componentFixed_iInf_normalizes (w : LocalControlWitness T M) (L : Subgroup G) :
    M ≤ normalizer ((⨅ a : M, componentFixedSubgroup w (componentConjugate L a) : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro m hm v hv
  apply mem_iInf.mpr
  intro a
  have hv' := mem_iInf.mp hv ((⟨m, hm⟩ : M)⁻¹ * a)
  refine ⟨(mem_normalizer_iff.mp (w.normalizes hm) v).mp hv'.1, ?_⟩
  intro l hl
  have hl' : m⁻¹ * l * m ∈ componentConjugate L ((⟨m, hm⟩ : M)⁻¹ * a) := by
    obtain ⟨k, hk, rfl⟩ := hl
    refine ⟨k, hk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have he := congrArg (MulAut.conj m) (hv'.2 (m⁻¹ * l * m) hl')
  simpa [MulAut.conj_apply, mul_assoc] using he

/-- The order/intersection argument of p.520. The last two inputs are the
component-balance and local odd-rank obligations, not TI assumptions. -/
private theorem component_eq_of_fixed_intersection (w : LocalControlWitness T M)
    (L : Subgroup G) (hLM : ¬ L ≤ M)
    (hsplit : w.U = componentFixedSubgroup w L ⊔ (w.U ⊓ L))
    (hcomm : ∀ x y : M,
      componentFixedSubgroup w (componentConjugate L x) ⊓
        componentFixedSubgroup w (componentConjugate L y) ≠ ⊥ →
      componentConjugate L x ≠ componentConjugate L y →
      componentConjugate L x ≤ centralizer (componentConjugate L y : Set G))
    (hthree : ∀ x y z : M,
      componentConjugate L x ≠ componentConjugate L y →
      componentConjugate L x ≠ componentConjugate L z →
      componentConjugate L y ≠ componentConjugate L z →
      componentConjugate L x ≤ centralizer (componentConjugate L y : Set G) →
      componentConjugate L x ≤ centralizer (componentConjugate L z : Set G) →
      componentConjugate L y ≤ centralizer (componentConjugate L z : Set G) → False)
    (x y : M)
    (hxy : componentFixedSubgroup w (componentConjugate L x) ⊓
      componentFixedSubgroup w (componentConjugate L y) ≠ ⊥) :
    componentConjugate L x = componentConjugate L y := by
  classical
  let _ : IsElementaryAbelian 2 w.U := w.elementary
  let A : M → Subgroup G := fun a => componentFixedSubgroup w (componentConjugate L a)
  have hle (a : M) : A a ≤ w.U := inf_le_left
  have hcard (a : M) : Nat.card (A a) = Nat.card (componentFixedSubgroup w L) := by
    dsimp [A]
    rw [componentFixedSubgroup_conjugate]
    exact card_map_of_injective (MulAut.conj (a : G)).injective
  have hnorm (a b : M) : A b ≤ normalizer (A a : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact (hle b).trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (hle a)))
  have hprod (a b : M) :
      Nat.card (componentFixedSubgroup w L) * Nat.card (componentFixedSubgroup w L) =
        Nat.card (A a ⊓ A b : Subgroup G) * Nat.card (A a ⊔ A b : Subgroup G) := by
    simpa only [hcard] using card_mul_eq_card_inf_mul_card_sup_of_normalizes (A a) (A b) (hnorm a b)
  by_contra hne
  have hsplitx : w.U = A x ⊔ (w.U ⊓ componentConjugate L x) := by
    have hu : componentConjugate w.U x = w.U :=
      mem_normalizer_iff_map_conj_eq.mp (w.normalizes x.property)
    have he := congrArg (fun D : Subgroup G => componentConjugate D x) hsplit
    rw [hu] at he
    change w.U = (componentFixedSubgroup w L ⊔ (w.U ⊓ L)).map
      (MulAut.conj (x : G)).toMonoidHom at he
    rw [Subgroup.map_sup, Subgroup.map_inf w.U L _ (MulAut.conj (x : G)).injective] at he
    change w.U = componentConjugate (componentFixedSubgroup w L) x ⊔
      (componentConjugate w.U x ⊓ componentConjugate L x) at he
    rw [hu, ← componentFixedSubgroup_conjugate] at he
    exact he
  have hsup : A x ⊔ A y = w.U := by
    apply le_antisymm (sup_le (hle x) (hle y))
    rw [hsplitx]
    apply sup_le le_sup_left
    exact (le_inf inf_le_left (inf_le_right.trans (hcomm x y hxy hne))).trans le_sup_right
  have hbig : Nat.card w.U < Nat.card (componentFixedSubgroup w L) *
      Nat.card (componentFixedSubgroup w L) := by
    rw [hprod x y, hsup]
    have hi := (one_lt_card_iff_ne_bot (H := A x ⊓ A y)).mpr hxy
    have hp : 0 < Nat.card w.U := Nat.card_pos
    nlinarith
  have hinter (a b : M) : A a ⊓ A b ≠ ⊥ := by
    intro he
    have hp := hprod a b
    rw [he, card_bot, one_mul] at hp
    have hc := card_le_of_le (sup_le (hle a) (hle b))
    omega
  have htwo (a : M) : componentConjugate L a = componentConjugate L x ∨
      componentConjugate L a = componentConjugate L y := by
    by_contra he
    push Not at he
    exact hthree x y a hne he.1.symm he.2.symm
      (hcomm x y (hinter x y) hne)
      (hcomm x a (hinter x a) he.1.symm)
      (hcomm y a (hinter y a) he.2.symm)
  let V : Subgroup G := ⨅ a : M, A a
  have hV : V = A x ⊓ A y := by
    apply le_antisymm (le_inf (iInf_le _ x) (iInf_le _ y))
    apply le_iInf
    intro a
    rcases htwo a with ha | ha
    · change _ ≤ componentFixedSubgroup w (componentConjugate L a)
      rw [ha]
      exact inf_le_left
    · change _ ≤ componentFixedSubgroup w (componentConjugate L a)
      rw [ha]
      exact inf_le_right
  have hMV : M ≤ normalizer (V : Set G) := componentFixed_iInf_normalizes w L
  have hVU : V ≤ w.U := (iInf_le _ (1 : M)).trans (hle 1)
  rcases w.minimal V hVU hMV with hb | ht
  · exact hxy (hV.symm.trans hb)
  · have hUA : w.U ≤ componentFixedSubgroup w L := by
      have hh : V ≤ A 1 := iInf_le _ 1
      simpa only [ht, A, componentConjugate_one] using hh
    exact componentFixedSubgroup_ne_self w L hLM (le_antisymm inf_le_left hUA)


open Theory.GroupTheory

/-- Components of the bad involution centralizers, retained in G. -/
def badCentralizerComponents (w : LocalControlWitness T M) : Set (Subgroup G) :=
  {L | ¬ L ≤ M ∧ ∃ u ∈ w.U, u ≠ 1 ∧
    IsComponentIn L (centralizer ({u} : Set G))}

/-- The source's maximal choice uses inclusion among genuine components. -/
theorem exists_maximal_badCentralizerComponent (w : LocalControlWitness T M)
    (hne : (badCentralizerComponents w).Nonempty) :
    ∃ L, Maximal (fun K => K ∈ badCentralizerComponents w) L :=
  Set.Finite.exists_maximal (Set.toFinite _) hne

omit [Finite G] in
/-- The containment conclusion needed from I.3.2 becomes component equality
by the maximal choice. In particular, balance is not replaced by a TI input. -/
theorem maximal_component_in_centralizer (w : LocalControlWitness T M)
    {L : Subgroup G} (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L)
    {v : G} (hv : v ∈ componentFixedSubgroup w L) (hv1 : v ≠ 1)
    (hbalance : ∃ K : Subgroup G,
      IsComponentIn K (centralizer ({v} : Set G)) ∧ L ≤ K) :
    IsComponentIn L (centralizer ({v} : Set G)) := by
  obtain ⟨K, hK, hLK⟩ := hbalance
  have hbad : K ∈ badCentralizerComponents w :=
    ⟨fun hKM => hmax.1.1 (hLK.trans hKM), v, hv.1, hv1, hK⟩
  have he : L = K := le_antisymm hLK (hmax.2 hbad hLK)
  exact he.symm ▸ hK

omit [Finite G] in
private theorem map_singleton_centralizer (e : G ≃* G) (v : G) :
    (centralizer ({v} : Set G)).map e.toMonoidHom = centralizer ({e v} : Set G) := by
  apply le_antisymm
  · rintro a ⟨b, hb, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (mem_centralizer_singleton_iff.mp hb)
  · intro a ha
    refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp ha

omit [Finite G] in
/-- The selected component remains a component of each centralizer of a
nonidentity vector fixed by the corresponding conjugate. -/
theorem component_in_conjugate_centralizer (w : LocalControlWitness T M)
    (L : Subgroup G)
    (hselected : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      IsComponentIn L (centralizer ({v} : Set G)))
    (x : M) {v : G} (hv : v ∈ componentFixedSubgroup w (componentConjugate L x))
    (hv1 : v ≠ 1) : IsComponentIn (componentConjugate L x) (centralizer ({v} : Set G)) := by
  rw [componentFixedSubgroup_conjugate] at hv
  obtain ⟨a, ha, he⟩ := hv
  have ha1 : a ≠ 1 := by
    intro he1
    subst a
    exact hv1 (by simpa using he.symm)
  have hh := (hselected a ha ha1).map (MulAut.conj (x : G))
  change (MulAut.conj (x : G)) a = v at he
  rw [map_singleton_centralizer, he] at hh
  exact hh

omit [Finite G] in
/-- Intersecting fixed spaces put both distinct components in the same
literal involution centralizer, so ordinary-component calculus applies. -/
theorem component_commutes_of_fixed_intersection (w : LocalControlWitness T M)
    (L : Subgroup G)
    (hselected : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      IsComponentIn L (centralizer ({v} : Set G)))
    (x y : M)
    (hxy : componentFixedSubgroup w (componentConjugate L x) ⊓
      componentFixedSubgroup w (componentConjugate L y) ≠ ⊥)
    (hne : componentConjugate L x ≠ componentConjugate L y) :
    componentConjugate L x ≤ centralizer (componentConjugate L y : Set G) := by
  obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hxy
  have hv := v.property
  have hv1 : (v : G) ≠ 1 := fun he => hvne (Subtype.ext he)
  exact commutator_eq_bot_iff_le_centralizer.mp
    ((component_in_conjugate_centralizer w L hselected x hv.1 hv1).commutator_eq_bot_of_ne
      (component_in_conjugate_centralizer w L hselected y hv.2 hv1) hne)

/-- Source component rigidity. The rank obstruction is explicitly inside an
actual two-local of G, not an unrestricted prime-rank hypothesis on G. -/
theorem component_eq_of_twoLocal_rank (w : LocalControlWitness T M)
    (hqt : IsQuasithin G) (L : Subgroup G) (hLM : ¬ L ≤ M)
    (hsplit : w.U = componentFixedSubgroup w L ⊔ (w.U ⊓ L))
    (hselected : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      IsComponentIn L (centralizer ({v} : Set G)))
    (hthree : ∀ x y z : M,
      componentConjugate L x ≠ componentConjugate L y →
      componentConjugate L x ≠ componentConjugate L z →
      componentConjugate L y ≠ componentConjugate L z →
      componentConjugate L x ≤ centralizer (componentConjugate L y : Set G) →
      componentConjugate L x ≤ centralizer (componentConjugate L z : Set G) →
      componentConjugate L y ≤ centralizer (componentConjugate L z : Set G) →
      ∃ H : Subgroup G, IsTwoLocal H ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 ≤ primeRank p H)
    (x y : M)
    (hxy : componentFixedSubgroup w (componentConjugate L x) ⊓
      componentFixedSubgroup w (componentConjugate L y) ≠ ⊥) :
    componentConjugate L x = componentConjugate L y := by
  apply component_eq_of_fixed_intersection w L hLM hsplit
    (component_commutes_of_fixed_intersection w L hselected) _ x y hxy
  intro a b c hab hac hbc hAB hAC hBC
  obtain ⟨H, hH, p, hp, ho, hr⟩ := hthree a b c hab hac hbc hAB hAC hBC
  have hb := (isQuasithin_iff_twoLocal.mp hqt) H hH p hp ho
  omega

omit [Finite G] in
/-- A component in a bad centralizer has nontrivial fixed subgroup. -/
theorem componentFixedSubgroup_ne_bot_of_bad (w : LocalControlWitness T M)
    {L : Subgroup G} (hL : L ∈ badCentralizerComponents w) :
    componentFixedSubgroup w L ≠ ⊥ := by
  obtain ⟨_, u, hu, hu1, hc⟩ := hL
  intro he
  apply hu1
  have huf : u ∈ componentFixedSubgroup w L := by
    refine ⟨hu, ?_⟩
    intro l hl
    exact mem_centralizer_singleton_iff.mp (hc.1 hl)
  simpa only [he, mem_bot] using huf


end CFSG.Quasithin.Chapter2.BenderFusion
