module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportMultiplicity
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionStrictCost

/-!
# Displacement and movement from three natural support copies

Three constituent degrees in the literal commuting-component orbit supply
three disjoint translates of the irreducible support seed. An actor
centralizing that component acts identically on the three copies. Their
addition map is an equivariant embedding, so their fixed codimensions add.
The marked odd-degree natural SL₃ seed costs at least one field degree.
Applying this to the exchanged orbit gives six degrees for the same actor.

If the original starred actor centralized the chosen component, its image
on the pair would have the same kernel as its image on the seed. The latter
has rank at most twice the support field degree. D.2.5's inherited cubic
bound contradicts the six-degree cost, proving the movement required by
D.3.18. No containment of the actor in the support is assumed.

The literal Chapter12 application is
`SeedAlternativesMovedExhaustionSupportDisplacement`. The remaining field
comparison, Suzuki branch, orbit exhaustion and Source325 assembly remain
with this owner. Source: Aschbacher--Smith D.3.18--19 and D.3.10, printed
pp.203--204; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
set_option backward.isDefEq.respectTransparency false
open ChapterB.QuasisimpleSource
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

private theorem orbit_three_disjoint (ρ : Representation (ZMod 2) H E)
    (X K : Subgroup H) [X.Normal] (R : Submodule (ZMod 2) E)
    (hR : X ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation)
    (hd : 3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R)) :
    ∃ k l : K, Disjoint R (R.map (ρ k)) ∧
      Disjoint (R ⊔ R.map (ρ k)) (R.map (ρ l)) := by
  let I := invariantSubspace ρ X R hR
  have ha : IsAtom I := (Subrepresentation.irreducible_iff_isAtom I).mp hi
  have hp : 0 < Module.finrank (ZMod 2) R := by
    let := hi
    have hn : I.toSubmodule ≠ ⊥ := fun hh => ha.1 (Subrepresentation.toSubmodule_injective hh)
    exact Nat.pos_of_ne_zero (fun hh => hn (Submodule.finrank_eq_zero.mp hh))
  have hex (Q : Subrepresentation (ρ.comp X.subtype))
      (hQ : Module.finrank (ZMod 2) Q.toSubmodule < Module.finrank (ZMod 2) (orbitSpan ρ K R)) :
      ∃ k : K, Disjoint Q.toSubmodule (R.map (ρ k)) := by
    have hn : ¬ orbitSpan ρ K R ≤ Q.toSubmodule := by
      intro hh
      exact (not_le_of_gt hQ) (Submodule.finrank_mono hh)
    obtain ⟨k,hk⟩ : ∃ k : K, ¬ R.map (ρ k) ≤ Q.toSubmodule := by
      by_contra! hh
      exact hn (iSup_le hh)
    let J := conjugateSubrepresentationOrderIso ρ X k I
    have hj : IsAtom J := ((conjugateSubrepresentationOrderIso ρ X k).isAtom_iff I).mpr ha
    have hnJ : ¬ J ≤ Q := by
      change ¬ J.toSubmodule ≤ Q.toSubmodule
      simpa only [J,conjugateSubrepresentationOrderIso_toSubmodule] using (show ¬ I.toSubmodule.map (ρ k) ≤ Q.toSubmodule from hk)
    have hh := congrArg Subrepresentation.toSubmodule (hj.not_le_iff_disjoint.mp hnJ).eq_bot
    refine ⟨k,disjoint_iff.mpr ?_⟩
    change J.toSubmodule ⊓ Q.toSubmodule = ⊥ at hh
    rw [show J.toSubmodule = R.map (ρ k) from conjugateSubrepresentationOrderIso_toSubmodule ρ X k I,inf_comm] at hh
    exact hh
  obtain ⟨k,hk⟩ := hex I (by change Module.finrank (ZMod 2) R < _; omega)
  change Disjoint R (R.map (ρ k)) at hk
  let J := conjugateSubrepresentationOrderIso ρ X k I
  have he : J.toSubmodule = R.map (ρ k) := by
    simp only [J,conjugateSubrepresentationOrderIso_toSubmodule]; rfl
  have hs := Submodule.finrank_sup_add_finrank_inf_eq R (R.map (ρ k))
  rw [hk.eq_bot,finrank_bot,add_zero,finrank_map_action] at hs
  obtain ⟨l,hl⟩ := hex (I ⊔ J) (by
    change Module.finrank (ZMod 2) (R ⊔ J.toSubmodule : Submodule (ZMod 2) E) < _
    rw [he]
    omega)
  change Disjoint (I.toSubmodule ⊔ J.toSubmodule) (R.map (ρ l)) at hl
  rw [he] at hl
  exact ⟨k,l,hk,hl⟩


omit [FiniteDimensional (ZMod 2) E] in
private theorem commute_operator (ρ : Representation (ZMod 2) H E)
    {A K : Subgroup H} (hc : A ≤ centralizer (K : Set H)) (a : A) (k : K) (v : E) :
    ρ a (ρ k v) = ρ k (ρ a v) := by
  rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
  exact congrArg (fun g => ρ g v) ((hc a.property) k k.property).symm

/-- A centralizing actor pays the cost of at least three seed copies. -/
theorem commuting_orbit_triple_fixedCodim (ρ : Representation (ZMod 2) H E)
    (X K A : Subgroup H) [X.Normal] (R Y : Submodule (ZMod 2) E)
    (hR : X ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation)
    (hd : 3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R))
    (hAY : A ≤ subspaceStabilizer ρ Y) (hRY : orbitSpan ρ K R ≤ Y)
    (hAR : A ≤ subspaceStabilizer ρ R) (hc : A ≤ centralizer (K : Set H)) :
    3 * fixedCodim (invariantSubspace ρ A R hAR).toRepresentation ⊤ ≤
      fixedCodim (invariantSubspace ρ A Y hAY).toRepresentation ⊤ := by
  obtain ⟨k,l,hk,hl⟩ := orbit_three_disjoint ρ X K R hR hi hd
  let σ := (invariantSubspace ρ A R hAR).toRepresentation
  let τ := (invariantSubspace ρ A Y hAY).toRepresentation
  let u : (R × R) →ₗ[ZMod 2] E := R.subtype.coprod ((ρ k).comp R.subtype)
  let v : ((R × R) × R) →ₗ[ZMod 2] E := u.coprod ((ρ l).comp R.subtype)
  have hu (w : R × R) : u w ∈ R ⊔ R.map (ρ k) :=
    Submodule.add_mem_sup w.1.property ⟨w.2,w.2.property,rfl⟩
  have hvY (w : (R × R) × R) : v w ∈ Y := by
    apply Y.add_mem
    · exact Y.add_mem (hRY (le_orbitSpan ρ K R w.1.1.property))
        (hRY ((le_iSup (fun k : K => R.map (ρ k)) k) ⟨w.1.2,w.1.2.property,rfl⟩))
    · exact hRY ((le_iSup (fun l : K => R.map (ρ l)) l) ⟨w.2,w.2.property,rfl⟩)
  let f : ((R × R) × R) →ₗ[ZMod 2] Y := v.codRestrict Y hvY
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro w hw
    have he : u w.1 + ρ l w.2.val = 0 := congrArg Subtype.val hw
    have hu0 : u w.1 = 0 := Submodule.disjoint_def.mp hl _ (hu w.1) (by
      rw [eq_neg_of_add_eq_zero_left he]
      exact (R.map (ρ l)).neg_mem ⟨w.2,w.2.property,rfl⟩)
    have hw2 : w.2 = 0 := by
      apply Subtype.ext
      apply (apply_bijective ρ l).injective
      simpa only [hu0,ZeroMemClass.coe_zero,zero_add,map_zero] using he
    have he1 : w.1.1.val + ρ k w.1.2.val = 0 := hu0
    have hw11 : w.1.1 = 0 := Subtype.ext (Submodule.disjoint_def.mp hk _ w.1.1.property (by
      rw [eq_neg_of_add_eq_zero_left he1]
      exact (R.map (ρ k)).neg_mem ⟨w.1.2,w.1.2.property,rfl⟩))
    have hw12 : w.1.2 = 0 := by
      apply Subtype.ext
      apply (apply_bijective ρ k).injective
      simpa only [hw11,ZeroMemClass.coe_zero,zero_add,map_zero] using he1
    exact Prod.ext (Prod.ext hw11 hw12) hw2
  have hb := fixedCodim_map_le_of_embedding τ ((σ.prod σ).prod σ)
    (MonoidHom.id A) f hf (by
      intro a w
      apply Subtype.ext
      change ρ a (w.1.1.val + ρ k w.1.2.val + ρ l w.2.val) =
        ρ a w.1.1.val + ρ k (ρ a w.1.2.val) + ρ l (ρ a w.2.val)
      rw [map_add,map_add,commute_operator ρ hc,commute_operator ρ hc]) ⊤
  simp only [Subgroup.map_id,fixedCodim_prod] at hb
  change 3 * fixedCodim σ ⊤ ≤ fixedCodim τ ⊤
  omega

/-- A nontrivial two-actor on an odd-degree natural support costs at least
one field degree on the original seed. -/
theorem natural_support_fixedCodim_ge (ρ : Representation (ZMod 2) H E)
    (X A : Subgroup H) [X.Normal] [IsQuasisimple X]
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlus ρ X R)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (invariantSubspace ρ X R hR.choose).toRepresentation (linearNatural F 3))
    (hA : IsPGroup 2 A) (hAR : A ≤ subspaceStabilizer ρ R)
    (hn : ¬ R ≤ fixedSpace ρ A) :
    F.degree ≤ fixedCodim (invariantSubspace ρ A R hAR).toRepresentation ⊤ := by
  obtain ⟨f,hf,_,_⟩ := exists_inner_lift_of_odd_linearThree ρ X R hR.choose
    (hR.not_le_fixedSpace ρ) F ho e A hAR hA
  let σ := (invariantSubspace ρ A R hAR).toRepresentation
  let g := e.groupEquiv.toMonoidHom.comp f
  have he := fixedCodim_map_equivariant σ (linearNatural F 3) g e.linearEquiv (by
    intro a v
    have hh := e.intertwines (f a) v
    have hv : (invariantSubspace ρ X R hR.choose).toRepresentation (f a) v = σ a v :=
      Subtype.ext (hf a v)
    rw [hv] at hh
    exact hh) ⊤
  have hp : 0 < fixedCodim σ ⊤ := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh := (fixedCodim_eq_zero_iff σ ⊤).mp hz
    apply hn
    intro v hv a
    exact congrArg Subtype.val ((hh.ge (Submodule.mem_top : (⟨v,hv⟩ : R) ∈ ⊤)) ⟨a,mem_top _⟩)
  rw [he,ChapterK.Linear.Natural.fixedCodim_eq_field_codim] at hp ⊢
  have hd : 0 < Module.finrank F.Carrier
      ((Fin 3 → F.Carrier) ⧸ ChapterK.Linear.Natural.fieldFixedSpace F 3 ((⊤ : Subgroup A).map g)) :=
    (Nat.pos_of_mul_pos_left hp)
  nlinarith

omit [FiniteDimensional (ZMod 2) E] in
private theorem orbit_conjugate (ρ : Representation (ZMod 2) H E)
    (K : Subgroup H) [K.Normal] (R : Submodule (ZMod 2) E) (t : H) :
    orbitSpan ρ K (R.map (ρ t)) = (orbitSpan ρ K R).map (ρ t) := by
  have he := orbitSpan_map_equivariant ρ ρ (MulAut.conj t).toMonoidHom (ρ t)
    (fun g v => by
      change ρ t (ρ g v) = ρ (t*g*t⁻¹) (ρ t v)
      simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]) K R
  have hk : K.map (MulAut.conj t).toMonoidHom = K := by
    apply le_antisymm
    · rintro _ ⟨k,hk,rfl⟩
      exact (inferInstance : K.Normal).conj_mem k hk t
    · intro k hk
      refine ⟨t⁻¹*k*t,by
        change t⁻¹*k*t ∈ K
        simpa only [inv_inv] using (inferInstance : K.Normal).conj_mem k hk t⁻¹,?_⟩
      change t*(t⁻¹*k*t)*t⁻¹=k
      group
  rw [hk] at he
  exact he.symm

omit [FiniteDimensional (ZMod 2) E] in
private theorem commuting_orbit_stable (ρ : Representation (ZMod 2) H E)
    (K A : Subgroup H) (R : Submodule (ZMod 2) E)
    (hR : A ≤ subspaceStabilizer ρ R) (hc : A ≤ centralizer (K : Set H)) :
    A ≤ subspaceStabilizer ρ (orbitSpan ρ K R) := by
  apply le_subspaceStabilizer
  intro a ha v hv
  change v ∈ ⨆ k : K, R.map (ρ k) at hv
  refine Submodule.iSup_induction (fun k : K => R.map (ρ k))
    (motive := fun w => ρ a w ∈ orbitSpan ρ K R) hv ?_ ?_ ?_
  · intro k w hw
    obtain ⟨r,hr,rfl⟩ := hw
    rw [commute_operator ρ hc ⟨a,ha⟩ k]
    exact (le_iSup (fun k : K => R.map (ρ k)) k) ⟨ρ a r,((hR ha) r).2 hr,rfl⟩
  · simpa only [map_zero] using (orbitSpan ρ K R).zero_mem
  · intro x y ihx ihy
    simpa only [map_add] using (orbitSpan ρ K R).add_mem ihx ihy

omit [FiniteDimensional (ZMod 2) E] in
private theorem invariant_cost_eq (ρ : Representation (ZMod 2) H E)
    (A : Subgroup H) (R : Submodule (ZMod 2) E)
    (hR : A ≤ subspaceStabilizer ρ R) :
    fixedCodim (invariantSubspace ρ A R hR).toRepresentation ⊤ =
      fixedCodim (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R A) := by
  have hh := fixedCodim_map_equivariant
    (invariantSubspace ρ A R hR).toRepresentation (subspaceImageRepresentation ρ R)
    (subgroupActionHom ρ R A hR) (LinearEquiv.refl _ _) (fun _ _ => rfl) ⊤
  rwa [←MonoidHom.range_eq_map,subgroupActionHom_range] at hh

/-- The centralizing subactor pays three field degrees in each original half.
All three copies come from the literal commuting-component orbit. -/
theorem support_pair_six_degree_displacement (ρ : Representation (ZMod 2) H E)
    (X K P B : Subgroup H) [X.Normal] [K.Normal] [IsQuasisimple X]
    (R I : Submodule (ZMod 2) E) (hR : IsIrrPlus ρ X R)
    (hPR : P ≤ subspaceStabilizer ρ R) (hBP : B ≤ P)
    (hB : IsPGroup 2 B) (hBK : B ≤ centralizer (K : Set H))
    (hXB : ⁅X,B⁆ = X)
    (F : BinaryField) (ho : Odd F.degree)
    (a : ActionEquiv (invariantSubspace ρ X R hR.choose).toRepresentation (linearNatural F 3))
    (hi : IsIrreducible (invariantSubspace ρ X R hR.choose).toRepresentation)
    (hd : 3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R))
    (hOI : orbitSpan ρ K R ≤ I) (t : H) (ht : t ∈ normalizer (P : Set H))
    (hdis : Disjoint I (I.map (ρ t))) :
    let O := orbitSpan ρ K R
    B ≤ subspaceStabilizer ρ (O ⊔ O.map (ρ t)) ∧
    6 * F.degree ≤ fixedCodim (subspaceImageRepresentation ρ (O ⊔ O.map (ρ t)))
      (restrictedSubgroup ρ (O ⊔ O.map (ρ t)) B) := by
  let O := orbitSpan ρ K R
  let Q := R.map (ρ t)
  have hBR := hBP.trans hPR
  have hBQ : B ≤ subspaceStabilizer ρ Q := by
    apply le_subspaceStabilizer
    rintro b hb _ ⟨v,hv,rfl⟩
    have hm : t⁻¹*b*t ∈ P := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp ((normalizer (P : Set H)).inv_mem ht) b).mp (hBP hb)
    refine ⟨ρ (t⁻¹*b*t) v,((hPR hm) v).2 hv,?_⟩
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hBO := commuting_orbit_stable ρ K B R hBR hBK
  have hBOt : B ≤ subspaceStabilizer ρ (O.map (ρ t)) := by
    rw [←orbit_conjugate ρ K R t]
    exact commuting_orbit_stable ρ K B Q hBQ hBK
  have hQ := hR.map_normalizer ρ (show t ∈ normalizer (X : Set H) by rw [normalizer_eq_top]; trivial)
  have aq := conjugate_linearThree_action ρ X (invariantSubspace ρ X R hR.choose) F a t
  have hqspace : (conjugateSubrepresentationOrderIso ρ X t
      (invariantSubspace ρ X R hR.choose)).toSubmodule = Q :=
    conjugateSubrepresentationOrderIso_toSubmodule ρ X t _
  have aq' : ActionEquiv (invariantSubspace ρ X Q hQ.choose).toRepresentation
      (linearNatural F 3) := by
    have he : conjugateSubrepresentationOrderIso ρ X t (invariantSubspace ρ X R hR.choose) =
        invariantSubspace ρ X Q hQ.choose := Subrepresentation.toSubmodule_injective hqspace
    rw [he] at aq
    exact aq
  have hiq := ExtensionConsequences.irreducible_of_equiv aq'
    (ExtensionConsequences.linearNatural_irreducible F (by decide))
  have hdq : 3 * Module.finrank (ZMod 2) Q ≤ Module.finrank (ZMod 2) (orbitSpan ρ K Q) := by
    dsimp only [Q]
    rw [orbit_conjugate,finrank_map_action,finrank_map_action]
    exact hd
  have hnR : ¬ R ≤ fixedSpace ρ B := by
    intro hh
    apply hR.not_le_fixedSpace ρ
    rw [←hXB]
    exact le_fixedSpace_commutator_of_invariant ρ hR.choose hh
  have hnQ : ¬ Q ≤ fixedSpace ρ B := by
    intro hh
    apply hQ.not_le_fixedSpace ρ
    rw [←hXB]
    exact le_fixedSpace_commutator_of_invariant ρ hQ.choose hh
  have hcR := natural_support_fixedCodim_ge ρ X B R hR F ho a hB hBR hnR
  have hcQ := natural_support_fixedCodim_ge ρ X B Q hQ F ho aq' hB hBQ hnQ
  have hO := commuting_orbit_triple_fixedCodim ρ X K B R O hR.choose hi hd hBO le_rfl hBR hBK
  have hOt := commuting_orbit_triple_fixedCodim ρ X K B Q (O.map (ρ t)) hQ.choose hiq hdq hBOt
    (orbit_conjugate ρ K R t).le hBQ hBK
  rw [invariant_cost_eq ρ B O hBO] at hO
  rw [invariant_cost_eq ρ B (O.map (ρ t)) hBOt] at hOt
  refine ⟨subspaceStabilizer_sup ρ hBO hBOt,?_⟩
  rw [common_actor_fixedCodim_sup ρ O (O.map (ρ t)) B hBO hBOt
    (hdis.mono hOI (Submodule.map_mono hOI))]
  omega

omit [FiniteDimensional (ZMod 2) E] in
private theorem commuting_orbit_kernel (ρ : Representation (ZMod 2) H E)
    (K A : Subgroup H) (R : Submodule (ZMod 2) E)
    (hc : A ≤ centralizer (K : Set H)) :
    subspaceKernel ρ (orbitSpan ρ K R) A = subspaceKernel ρ R A := by
  apply le_antisymm
  · exact fun a ha => ⟨ha.1,fun v hv => ha.2 v (le_orbitSpan ρ K R hv)⟩
  · intro a ha
    refine ⟨ha.1,fun v hv => ?_⟩
    change v ∈ ⨆ k : K, R.map (ρ k) at hv
    refine Submodule.iSup_induction (fun k : K => R.map (ρ k))
      (motive := fun w => ρ a w = w) hv ?_ ?_ ?_
    · intro k w hw
      obtain ⟨r,hr,rfl⟩ := hw
      rw [commute_operator ρ hc ⟨a,ha.1⟩ k,ha.2 r hr]
    · exact map_zero _
    · intro x y ihx ihy
      simp only [map_add,ihx,ihy]

/-- In the normal natural-support branch a starred actor must move the
commuting component. The proof uses the action image of the original actor
and does not assume its containment in the support. -/
theorem normal_support_starred_not_centralizing [Finite H]
    (ρ : Representation (ZMod 2) H E)
    (X K S P A : Subgroup H) [X.Normal] [K.Normal] [IsQuasisimple X]
    (hS : IsPGroup 2 S) (hPS : P ≤ S) (hSP : S ≤ normalizer (P : Set H))
    (hAP : A ≤ P) (hA : A ∈ ChapterD.QhatStar ρ)
    (hXB : ⁅X,A ⊓ centralizer (K : Set H)⁆ = X)
    (R I : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    (he : orbitSpan ρ P R = R)
    (F : BinaryField) (ho : Odd F.degree)
    (a : ActionEquiv (invariantSubspace ρ X R hR.invariant).toRepresentation (linearNatural F 3))
    (hi : IsIrreducible (invariantSubspace ρ X R hR.invariant).toRepresentation)
    (hd : 3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R))
    (hOI : orbitSpan ρ K R ≤ I) (t : H) (ht : t ∈ S)
    (hdis : Disjoint I (I.map (ρ t))) :
    ¬ A ≤ centralizer (K : Set H) := by
  intro hc
  have hXA : ⁅X,A⁆ = X := by simpa only [inf_eq_left.mpr hc] using hXB
  let O := orbitSpan ρ K R
  let Q := R.map (ρ t)
  let Y := O ⊔ O.map (ρ t)
  have hPR : P ≤ subspaceStabilizer ρ R := by rw [←he]; exact orbitSpan_invariant ρ P R
  have hAR := hAP.trans hPR
  have hAQ : A ≤ subspaceStabilizer ρ Q := by
    apply le_subspaceStabilizer
    rintro b hb _ ⟨v,hv,rfl⟩
    have hm : t⁻¹*b*t ∈ P := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp (hSP (S.inv_mem ht)) b).mp (hAP hb)
    refine ⟨ρ (t⁻¹*b*t) v,((hPR hm) v).2 hv,?_⟩
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hAO := commuting_orbit_stable ρ K A R hAR hc
  have hAOt : A ≤ subspaceStabilizer ρ (O.map (ρ t)) := by
    rw [←orbit_conjugate ρ K R t]
    exact commuting_orbit_stable ρ K A Q hAQ hc
  have hAY := subspaceStabilizer_sup ρ hAO hAOt
  have hn : ¬ R ≤ fixedSpace ρ A := by
    intro hh
    apply hR.isIrrPlus.not_le_fixedSpace ρ
    rw [←hXA]
    exact le_fixedSpace_commutator_of_invariant ρ hR.invariant hh
  have hRY : R ≤ Y := (le_orbitSpan ρ K R).trans le_sup_left
  have hYn : ¬ Y ≤ fixedSpace ρ A := fun hh => hn (hRY.trans hh)
  have hb := ChapterD.RPlusBound.restricted ρ
    (show A ∈ ChapterD.RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hA.1.1⟩,ChapterD.QhatStar.mem_RPlus ρ hA⟩)
    Y hAY hYn
  have hpair := homogeneous_support_pair_orbit_ff ρ X S P A A hS hPS hSP hAP le_rfl hXA hA
    R hR t ht (by
      rw [he]
      exact hdis.mono ((le_orbitSpan ρ K R).trans hOI)
        (Submodule.map_mono ((le_orbitSpan ρ K R).trans hOI)))
  have hkR : subspaceKernel ρ R A = subspaceKernel ρ Q A := by
    simpa only [he] using hpair.1.trans hpair.2.1.symm
  have hkY : subspaceKernel ρ Y A = subspaceKernel ρ R A := by
    apply le_antisymm
    · exact fun b hb => ⟨hb.1,fun v hv => hb.2 v (hRY hv)⟩
    · intro b hb
      have hO := (commuting_orbit_kernel ρ K A R hc).ge hb
      have hQ := (commuting_orbit_kernel ρ K A Q hc).ge (hkR.le hb)
      rw [orbit_conjugate ρ K R t] at hQ
      refine ⟨hb.1,fun v hv => ?_⟩
      obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add,hO.2 u hu,hQ.2 w hw]
  let := hA.1.2.1.2
  have hp := IsElementaryAbelian.isPGroup 2 A
  have rY := rank_subspaceKernel_add_image ρ Y A hAY hp
  have rR := rank_subspaceKernel_add_image ρ R A hAR hp
  rw [hkY] at rY
  have hr : rank (restrictedSubgroup ρ Y A) ≤ 2 * F.degree := by
    have hh := restricted_rank_le_odd_linearThree ρ X R hR.invariant F ho a A hAR hA.1.2.1.2
    omega
  have hcost := (support_pair_six_degree_displacement ρ X K P A R I hR.isIrrPlus
    hPR hAP hp hc hXA F ho a hi hd hOI t (hSP ht) hdis).2
  have hupper := (actionRatio_le_nat_iff (subspaceImageRepresentation ρ Y) hb.1 2).mp hb.2
  change 6 * F.degree ≤ fixedCodim (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) at hcost
  have hpos := F.degree_pos
  omega

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
