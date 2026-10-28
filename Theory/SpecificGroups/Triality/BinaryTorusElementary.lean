module
public import Theory.SpecificGroups.Triality.BinaryTorusCentralizer
import all Theory.SpecificGroups.Triality.BinaryTorusCentralizer

/-!
# Elementary subgroups of the binary-triality seven-centralizer

The existing torus calculation injects every fixed two-subgroup into the
three binary long-root coordinates. An abelian subgroup cannot attain order
eight: surjectivity of those coordinates would put both of the first two
long roots in it, whereas their commutator is the nonidentity highest root.
The two-power order therefore bounds an abelian subgroup by four. Sylow
conjugacy transports the bound to any seven-subgroup in the literal Borel.

The internal import intentionally reuses the preceding coordinate vanishing
calculation in this continuation of BinaryTorusCentralizer, preserving its
public boundary. No group enumeration or new matrix certificate is used.

Source: GLS3 §§2.4--2.6 for the folded-root exchange. The actual retained-core
application in Aschbacher--Smith 5.1.13, printed pp.635--638, is in
RankOneModuleGenericExceptionalCartanLocalBinaryElementaryKernel.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Triality.Standard.BinaryTorusCentralizer
open Parabolics PositiveCoordinates ConcreteBruhat
open RadicalCoordinates.LeviCommutators
open CentralCovers.TwoPrimary
local notation "P" => binaryParameters 1 Nat.zero_lt_one

private theorem long_two_ne_one : long P prime_two 2 1 ≠ 1 := by
  intro h
  have he : baseProduct 1 Nat.zero_lt_one (0, ![0,0,1]) =
      baseProduct 1 Nat.zero_lt_one 0 := by
    simp only [baseProduct]
    change short P prime_two 0 0 * long P prime_two 0 0 * short P prime_two 1 0 *
      short P prime_two 2 0 * long P prime_two 1 0 * long P prime_two 2 1 =
      short P prime_two 0 0 * long P prime_two 0 0 * short P prime_two 1 0 *
      short P prime_two 2 0 * long P prime_two 1 0 * long P prime_two 2 0
    simpa only [RadicalCoordinates.LeviCommutators.short_zero,
      RadicalCoordinates.LeviCommutators.long_zero, one_mul] using h
  have hz := congrFun (congrArg Prod.snd (baseProduct_injective 1 Nat.zero_lt_one he)) 2
  exact (one_ne_zero : (1 : fixedField P) ≠ 0) hz

private theorem long_pair_not_commute :
    ¬ Commute (long P prime_two 0 1) (long P prime_two 1 1) := by
  intro hc
  have he := long_zero_one_exchange P prime_two 1 1
  rw [hc.eq,one_mul] at he
  exact long_two_ne_one (mul_left_cancel (he.symm.trans (mul_one _).symm))

/-- An abelian two-subgroup of the standard seven-centralizer has order at most four. -/
theorem torus_abelian_two_subgroup_card_le_four
    (V : Subgroup (Carrier P)) (hV : IsPGroup 2 V) [IsMulCommutative V]
    (hVU : V ≤ unipotent P) (hVC : V ≤ centralizer (torus P : Set (Carrier P))) :
    Nat.card V ≤ 4 := by
  let f : V → Fin 3 → fixedField P := fun x =>
    ((positiveEquiv 1 Nat.zero_lt_one).symm ⟨x,hVU x.property⟩).2
  have hf : Function.Injective f := by
    intro x y he
    have hxy : (⟨x,hVU x.property⟩ : unipotent P) = ⟨y,hVU y.property⟩ := by
      apply (positiveEquiv 1 Nat.zero_lt_one).symm.injective
      apply Prod.ext
      · exact (short_zero_of_centralizes _ (hVC x.property)).trans
          (short_zero_of_centralizes _ (hVC y.property)).symm
      · exact he
    exact Subtype.ext (congrArg (fun z : unipotent P => (z : Carrier P)) hxy)
  have hsmall : Nat.card V < 8 := by
    by_contra hge
    have hsurj := (hf.bijective_of_nat_card_le (by
      rw [Nat.card_fun,card_fixedField,Nat.card_fin]
      exact Nat.le_of_not_gt hge)).2
    have hval (v : V) : (v : Carrier P) = baseProduct 1 Nat.zero_lt_one (0,f v) := by
      have he := congrArg Subtype.val ((positiveEquiv 1 Nat.zero_lt_one).apply_symm_apply
        ⟨v,hVU v.property⟩)
      rw [positiveEquiv_val] at he
      have hc := short_zero_of_centralizes ⟨v,hVU v.property⟩ (hVC v.property)
      exact he.symm.trans (congrArg (baseProduct 1 Nat.zero_lt_one)
        (Prod.ext hc rfl))
    obtain ⟨v,hv⟩ := hsurj ![1,0,0]
    obtain ⟨w,hw⟩ := hsurj ![0,1,0]
    have hv' : (v : Carrier P) = long P prime_two 0 1 := by
      rw [hval v,hv]
      simp only [baseProduct]
      change short P prime_two 0 0 * long P prime_two 0 1 * short P prime_two 1 0 *
        short P prime_two 2 0 * long P prime_two 1 0 * long P prime_two 2 0 = _
      simp only [RadicalCoordinates.LeviCommutators.short_zero,
        RadicalCoordinates.LeviCommutators.long_zero,one_mul,mul_one]
    have hw' : (w : Carrier P) = long P prime_two 1 1 := by
      rw [hval w,hw]
      simp only [baseProduct]
      change short P prime_two 0 0 * long P prime_two 0 0 * short P prime_two 1 0 *
        short P prime_two 2 0 * long P prime_two 1 1 * long P prime_two 2 0 = _
      simp only [RadicalCoordinates.LeviCommutators.short_zero,
        RadicalCoordinates.LeviCommutators.long_zero,one_mul,mul_one]
    have hc := (Commute.all v w).map V.subtype
    change Commute (v : Carrier P) (w : Carrier P) at hc
    rw [hv',hw'] at hc
    exact long_pair_not_commute hc
  obtain ⟨k,hk⟩ := hV.exists_card_eq
  rw [hk] at hsmall ⊢
  have hlt : k < 3 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hsmall
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : k ≤ 2))



/-- An elementary subgroup fixed by an actual seven in the Borel has order at most four. -/
theorem borel_elementary_subgroup_card_le_four
    (V E : Subgroup (borel P)) [IsElementaryAbelian 2 V] (hE : Nat.card E = 7)
    (hc : V ≤ centralizer (E : Set (borel P))) : Nat.card V ≤ 4 := by
  have hV := IsElementaryAbelian.isPGroup 2 V
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let C := (torus P).subgroupOf (borel P)
  have hC : Nat.card C = 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel P)).toEquiv,
      TorusCoordinates.card_torus P prime_two]
    rfl
  have hb : Nat.card (borel P) = 28672 := FixedCellCount.card_borel 1 Nat.zero_lt_one
  have hs (F : Subgroup (borel P)) (hF : Nat.card F = 7) :
      Nat.card F = 7 ^ (Nat.card (borel P)).factorization 7 := by
    rw [hF,hb]
    decide +kernel
  let Q : Sylow 7 (borel P) := Sylow.ofCard E (hs E hE)
  let Q₀ : Sylow 7 (borel P) := Sylow.ofCard C (hs C hC)
  obtain ⟨g,a,_,ha⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (borel P)) Q Q₀
  change E.map a.toMonoidHom = C at ha
  let f : borel P →* Carrier P := (borel P).subtype.comp a.toMonoidHom
  have hf : Function.Injective f := (borel P).subtype_injective.comp a.injective
  have hEf : E.map f = torus P := by
    rw [← map_map,ha,map_subgroupOf_eq_of_le (torus_le_borel P)]
  let U := (unipotentSylow P prime_two).subtype (unipotent_le_borel P)
  let : Unique (Sylow 2 (borel P)) := Sylow.unique_of_normal U (unipotent_normal_in_borel P prime_two)
  obtain ⟨Q₂,hQ₂⟩ := (hV.map a.toMonoidHom).exists_le_sylow
  have hV₂ : V.map a.toMonoidHom ≤ (unipotent P).subgroupOf (borel P) := by
    rw [Subsingleton.elim Q₂ U] at hQ₂
    exact hQ₂
  have hVU : V.map f ≤ unipotent P := by
    rw [← map_map]
    exact (map_mono hV₂).trans_eq (map_subgroupOf_eq_of_le (unipotent_le_borel P))
  have hVC : V.map f ≤ centralizer (torus P : Set (Carrier P)) := by
    rw [←hEf]
    exact (map_mono hc).trans (map_centralizer_le_centralizer_image E f)
  let : IsElementaryAbelian 2 (V.map f) := IsElementaryAbelian.map f
  have hh := torus_abelian_two_subgroup_card_le_four (V.map f) (hV.map f) hVU hVC
  rwa [card_map_of_injective hf] at hh

end Triality.Standard.BinaryTorusCentralizer
