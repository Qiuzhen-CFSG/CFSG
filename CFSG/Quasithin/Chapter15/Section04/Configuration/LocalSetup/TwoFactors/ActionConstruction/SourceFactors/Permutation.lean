module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors.Permutation.ResidualLift
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal.PairAction

/-!
# Conjugation of the actual residual factor pair

Given the compatible local quotient M → Q and its distinct order-three
factors, construct the actual ambient subgroups as the two-residuals of their
preimages. Quotient invariance constructs the conjugation permutation on
these subgroups. Quotient transitivity on T supplies an element of T which
interchanges both factors and lies outside the first factor's normalizer.
The original map is retained in the two-core quotient identifications and
in the conjugation of the actual modules [V(M), Lᵢ].

The algebraic assembly derives generation, relative X- and S-normalization,
two-perfectness, [Lᵢ,J]=Lᵢ and the order-three two-core quotients from the
corresponding whole-group and quotient facts. Only S-invariance is required
for the individual factors; no T-invariance or Y-family membership is asserted.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.2.3(1–2),
printed pp.216–217; 15.4.12(5–6), pp.1160–1161; first paragraph of 15.4.18,
p.1162. This module proves the conditional lifting and permutation step.
The genuine Y-family and E.2.3 interfaces have not yet supplied the chosen
quotient factors. In particular their preservation by all of M must still
be justified from the compatible module action, not from an abstract
isomorphism for XT/O₂(XT). Final source assembly remains open. No parent
SourceFactors import is used, so the parent can import this construction.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G Q : Type*} [Group G] [Group Q] [Finite G]

omit [Finite G] in
private theorem conjugate_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom =
      (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
/-- Construct the conjugation permutation of two distinct invariant subgroups. -/
noncomputable def pairAction_of_invariant (M : Subgroup G) (L : Bool → Subgroup G)
    (hinj : Function.Injective L)
    (hp : ∀ (g : M) i, ∃ j, (L i).map (MulAut.conj (g : G)).toMonoidHom = L j) :
    MixedLocal.FactorPairAction M L := by
  classical
  choose f hf using hp
  have hf_inj (g : M) : Function.Injective (f g) := by
    intro i j hij
    apply hinj
    apply map_injective (f := (MulAut.conj (g : G)).toMonoidHom)
      (MulAut.conj (g : G)).injective
    rw [hf, hf, hij]
  let e (g : M) : Equiv.Perm Bool := Equiv.ofBijective (f g)
    ⟨hf_inj g, Finite.surjective_of_injective (hf_inj g)⟩
  have he (g : M) (i : Bool) :
      (L i).map (MulAut.conj (g : G)).toMonoidHom = L (e g i) := hf g i
  refine ⟨hinj, { toFun := e, map_one' := ?_, map_mul' := ?_ }, he⟩
  · apply Equiv.ext
    intro i
    apply hinj
    rw [← he]
    rw [show (MulAut.conj ((1 : M) : G)).toMonoidHom = MonoidHom.id G by
      ext x; simp]
    exact map_id _
  · intro g h
    apply Equiv.ext
    intro i
    apply hinj
    change L (e (g * h) i) = L (e g (e h i))
    rw [← he (g * h) i, ← he g (e h i)]
    change (L i).map (MulAut.conj ((g : G) * (h : G))).toMonoidHom = _
    rw [conjugate_mul, he h i]

/-- The two intrinsic residual preimages, embedded into the original ambient group. -/
@[expose] def liftedFactors (M : Subgroup G) (q : M →* Q) (A : Bool → Subgroup Q) :
    Bool → Subgroup G := fun i => (residualPreimage q (A i)).map M.subtype

/-- The embedded factors retain the conjugation formula through the original local quotient. -/
theorem liftedFactors_conj (M : Subgroup G) (q : M →* Q) (A : Bool → Subgroup Q)
    (g : M) (i j : Bool) (he : (A i).map (MulAut.conj (q g)).toMonoidHom = A j) :
    (liftedFactors M q A i).map (MulAut.conj (g : G)).toMonoidHom =
      liftedFactors M q A j := by
  change ((residualPreimage q (A i)).map M.subtype).map _ = _
  have hh := congrArg (Subgroup.map M.subtype) (residualPreimage_conj q (A i) g)
  rw [he] at hh
  rw [map_map] at hh ⊢
  exact hh

/-- Distinct order-three quotient factors have distinct ambient residual lifts. -/
theorem liftedFactors_injective (M : Subgroup G) (q : M →* Q)
    (hq : Function.Surjective q) (A : Bool → Subgroup Q)
    (hA : ∀ i, Nat.card (A i) = 3) (hinj : Function.Injective A) :
    Function.Injective (liftedFactors M q A) := by
  intro i j he
  apply hinj
  have hh := congrArg (Subgroup.map q) (map_injective M.subtype_injective he)
  simpa only [residualPreimage_image q hq _ (three_isPPerfect _ (hA i)),
    residualPreimage_image q hq _ (three_isPPerfect _ (hA j))] using hh

/-- Construct an action on the actual ambient factors from invariance of their quotient factors. -/
noncomputable def liftedFactors_action (M : Subgroup G) (q : M →* Q)
    (hq : Function.Surjective q) (A : Bool → Subgroup Q)
    (hA : ∀ i, Nat.card (A i) = 3) (hinj : Function.Injective A)
    (hp : ∀ (g : M) i, ∃ j, (A i).map (MulAut.conj (q g)).toMonoidHom = A j) :
    MixedLocal.FactorPairAction M (liftedFactors M q A) :=
  pairAction_of_invariant M _ (liftedFactors_injective M q hq A hA hinj) (by
    intro g i
    obtain ⟨j, hj⟩ := hp g i
    exact ⟨j, liftedFactors_conj M q A g i j hj⟩)

/-- A quotient element interchanging the factors interchanges both ambient residual factors and lies outside their normalizers. -/
theorem liftedFactors_swap (M T : Subgroup G) (hTM : T ≤ M) (q : M →* Q)
    (hq : Function.Surjective q) (A : Bool → Subgroup Q)
    (hA : ∀ i, Nat.card (A i) = 3) (hinj : Function.Injective A)
    (hp : ∀ (g : M) i, ∃ j, (A i).map (MulAut.conj (q g)).toMonoidHom = A j)
    (htrans : ∃ t : T, (A false).map
      (MulAut.conj (q (inclusion hTM t))).toMonoidHom = A true) :
    ∃ t ∈ T, (liftedFactors M q A false).map (MulAut.conj t).toMonoidHom =
        liftedFactors M q A true ∧
      (liftedFactors M q A true).map (MulAut.conj t).toMonoidHom =
        liftedFactors M q A false ∧
      t ∉ normalizer (liftedFactors M q A false : Set G) := by
  obtain ⟨t, ht⟩ := htrans
  let a := liftedFactors_action M q hq A hA hinj hp
  have he := liftedFactors_conj M q A (inclusion hTM t) false true ht
  have hmove : a.permutation (inclusion hTM t) false = true :=
    a.distinct ((a.conjugation (inclusion hTM t) false).symm.trans he)
  have hother : a.permutation (inclusion hTM t) true = false := by
    cases hh : a.permutation (inclusion hTM t) true with
    | false => rfl
    | true =>
      have bad := (a.permutation (inclusion hTM t)).injective (hmove.trans hh.symm)
      cases bad
  refine ⟨(t : G), t.property, he, ?_, ?_⟩
  · exact (a.conjugation (inclusion hTM t) true).trans (congrArg _ hother)
  · intro hn
    have heq := mem_normalizer_iff_map_conj_eq.mp hn
    have bad := a.distinct (he.symm.trans heq)
    cases bad

/-- Lift relative normalization by a specified subgroup of the local overgroup. -/
theorem liftedFactors_normalized (M : Subgroup G) (q : M →* Q) (A : Bool → Subgroup Q)
    (U : Subgroup M) (i : Bool) (hn : U.map q ≤ normalizer (A i : Set Q)) :
    U.map M.subtype ≤ normalizer (liftedFactors M q A i : Set G) := by
  rintro _ ⟨u, hu, rfl⟩
  exact mem_normalizer_iff_map_conj_eq.mpr (liftedFactors_conj M q A u i i
    (mem_normalizer_iff_map_conj_eq.mp (hn (mem_map.mpr ⟨u, hu, rfl⟩))))

/-- Embedding the residual factors in the ambient group preserves two-perfectness. -/
theorem liftedFactors_perfect (M : Subgroup G) (q : M →* Q) (A : Bool → Subgroup Q)
    (i : Bool) : IsPPerfect 2 (liftedFactors M q A i) :=
  (residualPreimage_perfect q (A i)).of_surjective
    (M.subtype.subgroupMap _) (M.subtype.subgroupMap_surjective _)

/-- Identify the ambient factor two-core quotient while retaining the original local quotient map on every element. -/
theorem liftedFactors_quotient_compatible (M : Subgroup G) (q : M →* Q)
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (A : Bool → Subgroup Q) (i : Bool) (hA : Nat.card (A i) = 3) :
    ∃ e : (liftedFactors M q A i ⧸ pCore 2 (liftedFactors M q A i)) ≃* A i,
      ∀ x : liftedFactors M q A i,
        (e (QuotientGroup.mk' (pCore 2 (liftedFactors M q A i)) x) : Q) =
          q ⟨(x : G), map_subtype_le _ x.property⟩ := by
  obtain ⟨e, he⟩ := residualPreimage_quotient q hq hk (A i) hA
  let f := ((residualPreimage q (A i)).equivMapOfInjective M.subtype M.subtype_injective).symm
  let e' := (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  refine ⟨e', ?_⟩
  intro x
  change (e (QuotientGroup.mk' _ (f x)) : Q) = _
  rw [he]
  congr 1
  apply Subtype.ext
  have hh := congrArg Subtype.val (f.symm_apply_apply x)
  exact hh

/-- Both an actual quotient isomorphism and its order-three consequence for an ambient factor. -/
theorem liftedFactors_quotient (M : Subgroup G) (q : M →* Q)
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (A : Bool → Subgroup Q) (i : Bool) (hA : Nat.card (A i) = 3) :
    Nonempty ((liftedFactors M q A i ⧸ pCore 2 (liftedFactors M q A i)) ≃* A i) ∧
      Nat.card (liftedFactors M q A i ⧸ pCore 2 (liftedFactors M q A i)) = 3 := by
  obtain ⟨e, _⟩ := liftedFactors_quotient_compatible M q hq hk A i hA
  exact ⟨⟨e⟩, (Nat.card_congr e.toEquiv).trans hA⟩

/-- Assemble generation, relative X- and S-normalization, two-perfectness, commutator saturation and the intrinsic quotient orders. The application sets J=J(T) and S=Baum(T). -/
theorem liftedFactors_algebra (M : Subgroup G) (q : M →* Q)
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (X S J : Subgroup M) (hpX : IsPPerfect 2 X)
    (hX : q.ker ≤ normalizer (X : Set M)) (hJS : J ≤ S)
    (A : Bool → Subgroup Q) (hA : ∀ i, Nat.card (A i) = 3)
    (hinj : Function.Injective A) (hgen : A false ⊔ A true = X.map q)
    (hnX : ∀ i, X.map q ≤ normalizer (A i : Set Q))
    (hnS : ∀ i, S.map q ≤ normalizer (A i : Set Q)) (hc : ⁅X, J⁆ = X) :
    liftedFactors M q A false ⊔ liftedFactors M q A true = X.map M.subtype ∧
      ∀ i, X.map M.subtype ≤ normalizer (liftedFactors M q A i : Set G) ∧
        S.map M.subtype ≤ normalizer (liftedFactors M q A i : Set G) ∧
        IsPPerfect 2 (liftedFactors M q A i) ∧
        ⁅liftedFactors M q A i, J.map M.subtype⁆ = liftedFactors M q A i ∧
        Nat.card (liftedFactors M q A i ⧸ pCore 2 (liftedFactors M q A i)) = 3 := by
  have hjoin := residualPreimage_pair_join q hq hk X hpX hX A hA hgen hnX
  have hcomm := residualPreimage_pair_commutator q hq hk X J A hA hinj hgen hnX
    (fun i => (map_mono hJS).trans (hnS i)) hc
  refine ⟨?_, fun i => ⟨liftedFactors_normalized M q A X i (hnX i),
    liftedFactors_normalized M q A S i (hnS i), liftedFactors_perfect M q A i,
    ?_, (liftedFactors_quotient M q hq hk A i (hA i)).2⟩⟩
  · exact (Subgroup.map_sup _ _ _).symm.trans (congrArg (Subgroup.map M.subtype) hjoin)
  · exact (map_commutator _ _ _).symm.trans (congrArg (Subgroup.map M.subtype) (hcomm i))

open scoped Pointwise in
/-- The generated subgroup is the literal product of the two residual factors. Substituting the conjugation equality from liftedFactors_swap gives the product with a conjugate. -/
theorem liftedFactors_product (M : Subgroup G) (q : M →* Q)
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (X : Subgroup M) (hpX : IsPPerfect 2 X) (hX : q.ker ≤ normalizer (X : Set M))
    (A : Bool → Subgroup Q) (hA : ∀ i, Nat.card (A i) = 3)
    (hgen : A false ⊔ A true = X.map q)
    (hnX : ∀ i, X.map q ≤ normalizer (A i : Set Q)) :
    (X.map M.subtype : Set G) =
      (liftedFactors M q A false : Set G) * (liftedFactors M q A true : Set G) := by
  have hjoin : liftedFactors M q A false ⊔ liftedFactors M q A true = X.map M.subtype :=
    (Subgroup.map_sup _ _ _).symm.trans (congrArg (Subgroup.map M.subtype)
      (residualPreimage_pair_join q hq hk X hpX hX A hA hgen hnX))
  have hn : liftedFactors M q A false ≤ normalizer (liftedFactors M q A true : Set G) :=
    (hjoin ▸ le_sup_left).trans (liftedFactors_normalized M q A X true (hnX true))
  rw [← hjoin]
  exact coe_mul_of_left_le_normalizer_right _ _ hn

/-- Transport the actual modules [V,Lᵢ] under the same conjugation that permutes the factors. -/
theorem liftedFactors_module_conj (M : Subgroup G) (q : M →* Q) (A : Bool → Subgroup Q)
    (V : Subgroup G) (hnV : M ≤ normalizer (V : Set G))
    (g : M) (i j : Bool) (he : (A i).map (MulAut.conj (q g)).toMonoidHom = A j) :
    (⁅V, liftedFactors M q A i⁆).map (MulAut.conj (g : G)).toMonoidHom =
      ⁅V, liftedFactors M q A j⁆ := by
  have hv : V.map (MulAut.conj (g : G)).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (hnV g.property)
  rw [map_commutator, hv, liftedFactors_conj M q A g i j he]

/-- Quotient transitivity forces the restriction of the constructed ambient pair action to T to be nontrivial. -/
theorem liftedFactors_action_nontrivial (M T : Subgroup G) (hTM : T ≤ M) (q : M →* Q)
    (hq : Function.Surjective q) (A : Bool → Subgroup Q)
    (hA : ∀ i, Nat.card (A i) = 3) (hinj : Function.Injective A)
    (hp : ∀ (g : M) i, ∃ j, (A i).map (MulAut.conj (q g)).toMonoidHom = A j)
    (htrans : ∃ t : T, (A false).map
      (MulAut.conj (q (inclusion hTM t))).toMonoidHom = A true) :
    ((liftedFactors_action M q hq A hA hinj hp).restrict hTM).permutation ≠ 1 := by
  obtain ⟨t, ht, _, _, hn⟩ := liftedFactors_swap M T hTM q hq A hA hinj hp htrans
  let a := (liftedFactors_action M q hq A hA hinj hp).restrict hTM
  intro he
  have hk : (⟨t, ht⟩ : T) ∈ a.permutation.ker := by
    change a.permutation ⟨t, ht⟩ = 1
    rw [show a.permutation = 1 from he]
    rfl
  rw [a.kernel] at hk
  exact hn hk

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SourceFactors.Permutation
