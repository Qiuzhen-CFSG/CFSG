module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionQuotient
public import Theory.GroupTheory.ConjugatePairSeed.OrthogonalAction
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularPairCubicFixed
public import Theory.GroupTheory.QuaternionCentralProductNineAction.Quotient

/-!
# The cubic centralizer of the canonical equality core

The two conjugate elementary layers have order-two images in the literal
orthogonal action on P/Z(P). Since their canonical join has an S₃ quotient
and the action kernel is a two-group, those images form a non-two pair.
Their product is fixed-point-free on the square space. Taking its lift to
the 256th power removes the two-part, because |H| divides 768. A Sylow
three-subgroup containing that lift therefore centralizes only Z(P) in P.

The central line is fixed by all of H=C_G(z), giving equality. Both possible
orders of C_H(K) are retained. No recognition or transfer premise is used.
Source: Aschbacher–Smith, proof of 6.2.13, printed pp.687–688.
-/

open Subgroup Theory.GroupTheory
open scoped commutatorElement
public noncomputable section

private theorem singular_of_normalizes_elementary
    {B : Type*} [Group B] [Finite B] (P V : Subgroup B) [P.Normal]
    (d : QuaternionCentralProductData P) [IsElementaryAbelian 2 V]
    (hn : P ≤ normalizer (V : Set B)) (v : B) (hv : v ∈ V) :
    BinaryFourPlus.SingularDisplacements (d.quotientWreathAction (MulAut.conjNormal v)) := by
  apply d.wreath_singular_displacement
  intro p
  apply Subtype.ext
  change (v * (p : B) * v⁻¹ * (p : B)⁻¹)^2 = 1
  exact elemPow_eq_one_of_isElementaryAbelian _
    ((le_normalizer_iff_commutator_le_left.mp hn)
      (commutator_mem_commutator hv p.property))

private theorem sylow_cubic_of_singular_pair
    {B : Type*} [Group B] [Finite B] (P V : Subgroup B) [P.Normal]
    (d : QuaternionCentralProductData P) [IsElementaryAbelian 2 V]
    (hn : P ≤ normalizer (V : Set B)) (g : B)
    (hcard : Nat.card (V.map (d.quotientWreathAction.comp MulAut.conjNormal)) = 2)
    (hnot : ¬ IsPGroup 2 ((V ⊔ V.map (MulAut.conj g).toMonoidHom).map
      (d.quotientWreathAction.comp MulAut.conjNormal)))
    (hpow : ∀ x : B, x^768=1) :
    ∃ X : Sylow 3 B, P ⊓ centralizer (X : Set B) ≤ (center P).map P.subtype := by
  let f : B →* BinaryFourPlus.Wreath := d.quotientWreathAction.comp MulAut.conjNormal
  obtain ⟨a,ha1,_⟩ := (Nat.card_eq_two_iff' (1 : V.map f)).mp hcard
  obtain ⟨v,hv,hva⟩ := a.property
  have hvne : f v ≠ 1 := fun he => ha1 (Subtype.ext (hva ▸ he))
  have hVi : V.map f = zpowers (f v) := image_eq_zpowers_of_card_two V f hcard v hv hvne
  let w := g*v*g⁻¹
  have hw : w ∈ V.map (MulAut.conj g).toMonoidHom := mem_map_of_mem _ hv
  have him : (V.map (MulAut.conj g).toMonoidHom).map f = zpowers (f w) := by
    have he : f.comp (MulAut.conj g).toMonoidHom = (MulAut.conj (f g)).toMonoidHom.comp f := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
    rw [map_map,he,←map_map,hVi,MonoidHom.map_zpowers]
    simp only [w,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  have hv2 : v^2=1 := elemPow_eq_one_of_isElementaryAbelian v hv
  have hw2 : w^2=1 := by
    change (MulAut.conj g v)^2=1
    rw [←map_pow,hv2,map_one]
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  have hnW : P ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set B) := by
    have hp : P.map (MulAut.conj g).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (P : Set B) by
        rw [normalizer_eq_top];trivial)
    rw [←hp]
    exact (map_mono hn).trans (V.le_normalizer_map _)
  obtain ⟨h3,hfixed⟩ := BinaryFourPlus.singular_pair_cubic_fixed_free (f v) (f w)
    (by rw [←map_pow,hv2,map_one]) (by rw [←map_pow,hw2,map_one])
    (singular_of_normalizes_elementary P V d hn v hv)
    (singular_of_normalizes_elementary P _ d hnW w hw)
    (by change ¬IsPGroup 2 ((V ⊔ V.map (MulAut.conj g).toMonoidHom).map f) at hnot
        rw [Subgroup.map_sup,hVi,him] at hnot
        exact hnot)
  let x := (v*w)^256
  have hximage : f x = f v * f w := by
    change f ((v*w)^256)=_
    rw [map_pow,map_mul,←pow_mod_orderOf,h3]
    norm_num
  have hx3 : x^3=1 := by
    change ((v*w)^256)^3=1
    rw [←pow_mul]
    exact hpow (v*w)
  have hxne : x≠1 := by
    intro he
    have hh := hximage.symm.trans (congrArg f he)
    rw [map_one] at hh
    rw [hh,orderOf_one] at h3
    omega
  have hxorder : orderOf x=3 := orderOf_eq_prime hx3 hxne
  have hp3 : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hxorder];norm_num)
  obtain ⟨X,hX⟩ := hp3.exists_le_sylow
  refine ⟨X,?_⟩
  intro p hp
  let q : P := ⟨p,hp.1⟩
  have hcomm : x*p*x⁻¹=p := by
    rw [hp.2 x (hX (mem_zpowers x)),mul_inv_cancel_right]
  have hq : (MulAut.conjNormal x : MulAut P) q = q := Subtype.ext hcomm
  have hquo : quotientAut (center P) (MulAut.conjNormal x) (QuotientGroup.mk' (center P) q) =
      QuotientGroup.mk' (center P) q := by rw [quotientAut_apply_mk,hq]
  have hz := hfixed (d.squareCoordinates (Additive.ofMul (QuotientGroup.mk' (center P) q))) (by
    rw [←hximage]
    exact (d.squareCoordinates_quotientAut _ _).symm.trans (congrArg (fun u =>
      d.squareCoordinates (Additive.ofMul u)) hquo))
  have hzero : QuotientGroup.mk' (center P) q = 1 := by
    apply Additive.ofMul.injective
    exact d.squareCoordinates.injective (hz.trans (map_zero _).symm)
  exact ⟨q,(QuotientGroup.eq_one_iff _).mp hzero,rfl⟩

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- A Sylow three-subgroup of the original involution centralizer fixes
precisely the center of the canonical extraspecial core. -/
theorem LocalAnalysis.equality_cubic_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ∃ X : Sylow 3 (centralizer ({z} : Set G)),
      equalityCore L R z ⊓ centralizer (X : Set (centralizer ({z} : Set G))) =
        coreCenter (equalityCore L R z) := by
  let H := centralizer ({z} : Set G)
  let P := equalityCore L R z
  let K := equalityLayerClosure L R z
  let V := (layer L R).subgroupOf H
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  let d := hp.plusType.some
  let f : H →* BinaryFourPlus.Wreath := d.quotientWreathAction.comp MulAut.conjNormal
  have hker : f.ker = (equalityOuterAction L R z).ker := by
    ext x
    change d.quotientWreathAction (MulAut.conjNormal x) = 1 ↔ equalityOuterAction L R z x = 1
    rw [equalityOuterAction_apply]
    exact d.quotientWreathAction_eq_one_iff _
  have hkerQ : f.ker ≤ pCore 2 H := by
    rw [hker]
    exact A.equalityOuterAction_ker_le h611 hnatural hz hp.plusType
  have hPker : P ≤ f.ker := by
    rw [hker,A.equalityOuterAction_ker h611 hnatural hz hp.plusType]
    exact le_sup_left
  have hVH := layer_le_involution_centralizer h611 hz
  let := h611.layer_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  have hV16 : Nat.card V=16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv]
    exact hnatural.2.1.card
  have hVker : V ⊓ f.ker = V ⊓ pCore 2 H := by
    apply le_antisymm (inf_le_inf_left _ hkerQ)
    exact le_inf inf_le_left (fun x hx => hPker (by
      rw [show P=equalityCore L R z from rfl,equalityCore_eq_intersection]
      exact ⟨le_normalClosure hx.1,hx.2⟩))
  have h8 : Nat.card (V ⊓ f.ker : Subgroup H)=8 := by
    rw [hVker,←card_map_of_injective H.subtype_injective,map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hVH]
    exact A.layer_core_card
  have hfV : Nat.card (V.map f)=2 := card_image_two_of_sixteen_inf_kernel_eight V f hV16 h8
  obtain ⟨g,hg,_,hgen,_,_,_⟩ := hp.pair
  let gH : H := ⟨g,hg⟩
  have hK : V ⊔ V.map (MulAut.conj gH).toMonoidHom=K := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVH]
    have he : (V.map (MulAut.conj gH).toMonoidHom).map H.subtype =
        (layer L R).map (MulAut.conj g).toMonoidHom := by
      rw [map_map]
      have hh : H.subtype.comp (MulAut.conj gH).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp H.subtype := by ext x;rfl
      rw [hh,←map_map,map_subgroupOf_eq_of_le hVH]
    rw [he]
    exact hgen.symm
  have hn : P ≤ normalizer (V : Set H) := by
    intro p hpP
    apply (layer L R).le_normalizer_comap H.subtype
    exact h611.sylow_normalizes_layer (equalityCore_le_sylow hTH
      (mem_map_of_mem H.subtype hpP))
  have hnot : ¬IsPGroup 2 ((V ⊔ V.map (MulAut.conj gH).toMonoidHom).map f) := by
    rw [hK]
    intro hh
    have hkerp : IsPGroup 2 f.ker := pCore_isPGroup.to_le hkerQ
    have hKp : IsPGroup 2 K := (hh.comap_of_ker_isPGroup f hkerp).to_le (le_comap_map _ _)
    have hqp : IsPGroup 2 (K ⧸ pCore 2 K) :=
      hKp.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hs := hqp.of_equiv hp.quotient.some
    obtain ⟨m,hm⟩ := hs.exists_card_dvd_pow
    have h6 : Nat.card (Equiv.Perm (Fin 3))=6 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [h6] at hm
    have hd := Nat.prime_three.dvd_of_dvd_pow ((by decide : 3∣6).trans hm)
    norm_num at hd
  have hpow : ∀x:H,x^768=1 := by
    intro x
    apply orderOf_dvd_iff_pow_eq_one.mp
    apply (orderOf_dvd_natCard x).trans
    rw [A.equality_centralizer_order h611 hnatural hz horder hTH hbranch]
    rcases A.equality_centralizer_card h611 hnatural hz horder hTH hbranch with h2|h4
    · norm_num [h2]
    · norm_num [h4]
  obtain ⟨X,hX⟩ := sylow_cubic_of_singular_pair P V d hn gH hfV hnot hpow
  refine ⟨X,le_antisymm hX ?_⟩
  refine le_inf (map_subtype_le _) ?_
  rw [hp.core_center]
  exact (equalityLine_le_center z).trans (center_le_centralizer _)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
