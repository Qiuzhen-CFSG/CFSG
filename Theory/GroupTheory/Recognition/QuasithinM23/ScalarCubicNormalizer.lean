module
public import Theory.GroupTheory.Recognition.QuasithinM23.SemilinearQuotient
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.SylowNormalizerRank
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.GroupTheory.OddSubgroupLift
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
/-!
# Lifting the scalar cubic with its full local normalizer

Lift the normal scalar cubic of ΓL₂(4) through an elementary sixteen-kernel.
Every nontrivial scalar acts without nonzero fixed vectors on the actual
natural module. Therefore the lifted cubic's normalizer intersects the
kernel trivially. Coprime normalizer lifting makes its image the entire
semilinear quotient, giving both an actual complement and an equivalence
whose values are the original quotient map. The scalar-commutant theorem
also puts the lifted cubic in a Sylow three-subgroup of the literal
preimage of the centralizer of the marked SL₂ quotient.

Source application: the first sentence of Aschbacher–Smith 5.2.15,
printed pp.654–655 (`refs/quasithin.pdf`). This identifies the local
normalizer only; the full ambient normalizer remains a source obligation.
-/

public noncomputable section
open Subgroup
open Representation.SL2FourNatural Representation.SL2FourNatural.SemilinearNormalizer
namespace Theory.GroupTheory.QuasithinM23
private theorem natural_scalar (c : Fˣ) (v : V) : natural (scalar c) v = (c : F) • v := by
  rw [natural_apply]
  change (Matrix.GeneralLinearGroup.scalar (Fin 2) c).val.mulVec v = _
  rw [Matrix.GeneralLinearGroup.coe_scalar,Matrix.scalar_apply,Matrix.diagonal_const_mulVec]

private theorem scalar_injective : Function.Injective scalar := by
  intro a b hab
  have hh := congrArg (fun g : Gamma => natural g (fun _ => 1) 0) hab
  apply Units.ext
  simpa only [natural_scalar,Pi.smul_apply,smul_eq_mul,mul_one] using hh

private theorem scalar_card : Nat.card scalar.range = 3 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective scalar_injective).toEquiv,Nat.card_eq_fintype_card]
  exact card_labels

private theorem scalar_normal : scalar.range.Normal := by
  constructor
  rintro _ ⟨c,rfl⟩ g
  refine ⟨Units.map g.right.toMonoidHom c,?_⟩
  apply natural_injective
  apply LinearEquiv.ext
  intro v
  rw [natural_scalar,map_mul,map_mul,map_inv]
  change _ = natural g (natural (scalar c) ((natural g).symm v))
  rw [natural_scalar,natural_smul,LinearEquiv.apply_symm_apply]
  rfl

private theorem scalar_fixed {c : Fˣ} (hc : c ≠ 1) {v : V}
    (hv : natural (scalar c) v = v) : v = 0 := by
  rw [natural_scalar] at hv
  have h : ((c : F)-1) • v = 0 := by rw [sub_smul,one_smul,hv,sub_self]
  exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (fun h => hc (Units.ext h)))

private theorem scalar_centralizer :
    centralizer (special.range : Set Gamma) = scalar.range := by
  apply le_antisymm
  · intro g hg
    obtain ⟨c,hc⟩ := Representation.SL2NaturalOffenders.centralizer_scalar
      (natural g).toAddEquiv.toAddMonoidHom (fun k v => by
        change natural g (k.val.mulVec v) = k.val.mulVec (natural g v)
        have hh := congrArg (fun z : Gamma => natural z v) (hg (special k) ⟨k,rfl⟩)
        simpa only [map_mul,LinearEquiv.mul_apply,natural_special,action_apply] using hh.symm)
    have hc0 : c ≠ 0 := by
      intro hz
      have hh := hc (fun _ => 1)
      rw [hz,zero_smul] at hh
      have he := (natural g).injective (hh.trans (map_zero _).symm)
      have he' := congrFun he 0
      exact one_ne_zero he'
    refine ⟨Units.mk0 c hc0,?_⟩
    apply natural_injective
    apply LinearEquiv.ext
    intro v
    exact (natural_scalar (Units.mk0 c hc0) v).trans (hc v).symm
  · rintro _ ⟨c,rfl⟩ _ ⟨k,rfl⟩
    exact (scalar_special_commute c k).symm

/-- The scalar cubic lifts so that its actual normalizer is a complement
and is identified with the original semilinear quotient map. -/
theorem exists_scalar_cubic_normalizer
    {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16)
    (q : X →* Gamma) (hq : Function.Surjective q) (hk : q.ker = U)
    (b : Multiplicative V ≃* U)
    (hb : ∀ x v, (b (Multiplicative.ofAdd (natural (q x) v.toAdd)) : X) =
      x * (b v : X) * x⁻¹) :
    ∃ C : Subgroup X, C.map q = scalar.range ∧ Nat.card C = 3 ∧
      U.IsComplement' (Subgroup.normalizer (C : Set X)) ∧
      ∃ e : Subgroup.normalizer (C : Set X) ≃* Gamma,
        (∀ x : Subgroup.normalizer (C : Set X), e x = q x) ∧
        ∃ P : Sylow 3 ((centralizer (special.range : Set Gamma)).comap q),
          (P : Subgroup ((centralizer (special.range : Set Gamma)).comap q)).map
            ((centralizer (special.range : Set Gamma)).comap q).subtype = C := by
  let : Finite Gamma := Nat.finite_of_card_ne_zero (by rw [gamma_card]; decide)
  obtain ⟨C,hC,hinj,hcard,_⟩ := q.exists_odd_subgroup_lift hq
    (hk.symm ▸ IsElementaryAbelian.isPGroup 2 U) scalar.range (by rw [scalar_card]; decide)
  rw [scalar_card] at hcard
  have hfree (c : X) (hc : c ∈ C) (hc1 : c ≠ 1)
      (u : X) (hu : u ∈ U) (hcu : c*u = u*c) : u = 1 := by
    obtain ⟨a,ha⟩ := (show q c ∈ scalar.range from hC ▸ mem_map_of_mem q hc)
    have ha1 : a ≠ 1 := by
      intro hh
      have he : (⟨c,hc⟩ : C) = 1 := hinj (by change q c = q 1; rw [←ha,hh,map_one,map_one])
      exact hc1 (congrArg Subtype.val he)
    let v := b.symm ⟨u,hu⟩
    have hv : natural (scalar a) v.toAdd = v.toAdd := by
      apply Multiplicative.ofAdd.injective
      apply b.injective
      apply Subtype.ext
      rw [ha,hb,ofAdd_toAdd,b.apply_symm_apply]
      exact (mul_inv_eq_iff_eq_mul).mpr hcu
    have hz := scalar_fixed ha1 hv
    have hv1 : v = 1 := Multiplicative.toAdd.injective hz
    have hh := congrArg (fun w => (b w : X)) hv1
    simpa only [v,b.apply_symm_apply,map_one,coe_one] using hh
  have hdis : Disjoint U (Subgroup.normalizer (C : Set X)) := by
    apply disjoint_def.mpr
    intro u hu hun
    obtain ⟨c,hc,hc1⟩ := C.bot_or_exists_ne_one.resolve_left (by
      intro hh; rw [hh,card_bot] at hcard; omega)
    have hmem := (mem_normalizer_iff.mp hun c).mp hc
    have he : (⟨u*c*u⁻¹,hmem⟩ : C) = ⟨c,hc⟩ := hinj (by
      change q (u*c*u⁻¹) = q c
      simp only [map_mul,map_inv,show q u = 1 from (show u ∈ q.ker from hk.symm ▸ hu),one_mul,inv_one,mul_one])
    exact hfree c hc hc1 u hu (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  have hcp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hcard)
  let : Fact (IsPGroup 3 C) := ⟨hcp⟩
  let : scalar.range.Normal := scalar_normal
  let N := Subgroup.normalizer (C : Set X)
  have hmap : N.map q = ⊤ := by
    rw [←normalizer_map_eq_of_coprime_kernel 3 C q hq (by rw [hk,hU]; decide),hC]
    exact normalizer_eq_top _
  let r := q.comp N.subtype
  have hr : Function.Bijective r := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff r).mp
      rw [eq_bot_iff_forall]
      intro x hx
      exact Subtype.ext (disjoint_def.mp hdis (hk ▸ (show q x = 1 from hx)) x.property)
    · intro g
      obtain ⟨x,hx,hxg⟩ := (show g ∈ N.map q from hmap ▸ mem_top g)
      exact ⟨⟨x,hx⟩,hxg⟩
  have hcomplement : U.IsComplement' N := by
    refine isComplement'_of_card_mul_and_disjoint ?_ hdis
    rw [Nat.card_congr (MulEquiv.ofBijective r hr).toEquiv]
    have he := Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)).toEquiv
    rw [←he,←index_eq_card]
    exact U.card_mul_index
  let D := (centralizer (special.range : Set Gamma)).comap q
  have hCD : C ≤ D := by
    intro c hc
    change q c ∈ centralizer (special.range : Set Gamma)
    rw [scalar_centralizer,←hC]
    exact mem_map_of_mem q hc
  have hD : Nat.card D = 48 := by
    have hc := IsElementaryAbelian.card_inf_ker_mul_card_map D q
    rw [inf_eq_right.mpr (ker_le_comap q _),hk,hU,
      map_comap_eq_self_of_surjective hq,scalar_centralizer,scalar_card] at hc
    exact hc.symm
  let P : Sylow 3 D := Sylow.ofCard (C.subgroupOf D) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCD).toEquiv,hcard,hD]
    decide +kernel)
  exact ⟨C,hC,hcard,hcomplement,MulEquiv.ofBijective r hr,fun _ => rfl,
    P,map_subgroupOf_eq_of_le hCD⟩
end Theory.GroupTheory.QuasithinM23
