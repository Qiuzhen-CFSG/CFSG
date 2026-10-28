module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylActionModel
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity
public import Theory.SpecificGroups.Triality.RadicalCoordinates.ParabolicSplitting
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterTorus

/-!
# The marked triality arms root and its fixed noncore element

The torus fixed by the arms reflection has positive-subgroup centralizer
exactly the cubic-field simple root. The coordinates (b,b²), for a base-field
unit b, give weight one on that root and weights b or b² on all other
positive coordinates. Thus the calculation applies at every q>2, including
q=4. The actual parabolic Weyl-coset theorem makes this fixed torus invariant
under a torus-preserving parabolic automorphism.

Consequently such an automorphism, when it also preserves the original
positive subgroup, induces an additive equivalence on the cubic root. An
involutive additive equivalence in characteristic two has a nonzero fixed
parameter. The corresponding genuine root lies in the arms Levi and escapes
its disjoint radical. The companion source module transports this fixed
root through the original right-parabolic map and proves local Sylow
maximality, without assuming the full torus--coefficient action identity.

Source: Aschbacher--Smith F.4.29 and F.4.37--38, pp.289,293--294,
`refs/quasithin.pdf`; GLS3 §§2.3--2.6 for the descended D4 root coordinates.
The internal import reuses the checked coordinate weights within this
source family without changing their existing public boundary.
-/

public noncomputable section
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.PositiveCoordinates
open Triality.Standard.Parabolics.RankOneMatrices Triality.Standard.ElementaryCentralKernel
open Triality.Standard.OuterOdd.Coverage.ParameterRigidity
open Triality.Standard.CentralCovers.TwoPrimary
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityRootAction

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g*(x*y)*g⁻¹=(g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem torus_weyl_commute_iff (P : Parameters) (hp : P.prime=2)
    (v : TorusCoordinates.OrbitParameters P) (i : Node) :
    Commute (TorusCoordinates.torusMulEquiv P hp v).val (simpleRepresentative P hp i) ↔
      nodeCharacter P v i=1 := by
  let := rootField_charTwo P hp i
  let g := (TorusCoordinates.torusMulEquiv P hp v).val
  let c := (nodeCharacter P v i).val
  have hu (r : RootField P i) := rankOne_signed P hp true i r
  have hl (r : RootField P i) := rankOne_signed P hp false i r
  have hw : simpleRepresentative P hp i = rankOne P hp i (weyl 1) := by
    rw [simpleRepresentative_eq_root_word]
    simp only [weyl,map_mul,inv_one]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (hu 1).symm (hl 1).symm) (hu 1).symm
  have hc : g*simpleRepresentative P hp i*g⁻¹=rankOne P hp i (weyl c) := by
    rw [simpleRepresentative_eq_root_word,conjugate_mul,conjugate_mul]
    simp only [g,torus_root_conjugate,signedScalar,mul_one,weyl,map_mul]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (hu c).symm (hl c⁻¹).symm) (hu c).symm
  constructor
  · intro h
    have hh : g*simpleRepresentative P hp i*g⁻¹=simpleRepresentative P hp i := by
      rw [h.eq,mul_inv_cancel_right]
    have he : weyl c=weyl (1 : RootField P i) :=
      rankOne_injective P hp i (hc.symm.trans (hh.trans hw))
    have hv := congrArg (fun a => a (0 : Fin 2) 1) he
    rw [weyl_val c (nodeCharacter P v i).ne_zero,weyl_val 1 one_ne_zero] at hv
    exact Units.ext hv
  · intro h
    change g*simpleRepresentative P hp i=simpleRepresentative P hp i*g
    apply mul_inv_eq_iff_eq_mul.mp
    rw [hc,show c=1 from congrArg Units.val h,←hw]

private theorem arms_torus_character (P : Parameters) (b : (fixedField P)ˣ) :
    nodeCharacter P (TorusCoordinates.fixedUnit P b,b^2) .arms=1 := by
  simp [nodeCharacter,rootCharacters]

private theorem arms_fixed_weights (P : Parameters) (b : (fixedField P)ˣ)
    (j : Fin 12) :
    TrialityOuterTorus.rootWeight P
        (TorusCoordinates.expand P (TorusCoordinates.fixedUnit P b,b^2)) j =
      b.val.val ^ (if j.val<3 then (0 : ℕ) else if j.val=11 then 2 else 1) := by
  fin_cases j <;>
    simp only [TrialityOuterTorus.rootWeight,TrialityOuterTorus.root_pairing,
      TrialityOuterTorus.pairing,TorusCoordinates.expand,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      TorusCoordinates.frobenius_fixedUnit] <;>
    simp [TorusCoordinates.fixedUnit] <;> field_simp

private theorem arms_root_of_centralizes_fixed_torus (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (x : Carrier (binaryParameters n hn)) (hx : x∈unipotent (binaryParameters n hn))
    (hc : ∀ g : torus (binaryParameters n hn),
      Commute g.val (simpleRepresentative (binaryParameters n hn) rfl .arms) → Commute g.val x) :
    ∃ r : ExtensionField (binaryParameters n hn),
      x=rootElement (binaryParameters n hn) rfl true .arms r := by
  let P := binaryParameters n hn
  let v := (positiveEquiv n hn).symm ⟨x,hx⟩
  have hv : FixedDescent.carrierToSplit P rfl x=orderedProduct P (expand P v) := by
    rw [←baseProduct_toSplit]
    apply congrArg (FixedDescent.carrierToSplit P rfl)
    exact (congrArg Subtype.val ((positiveEquiv n hn).apply_symm_apply ⟨x,hx⟩)).symm.trans
      (positiveEquiv_val n hn v)
  have hq : 2<P.q := Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) hn2
  have hbcard : 1<Nat.card (fixedField P)ˣ := by rw [Nat.card_units,card_fixedField]; omega
  let : Nontrivial (fixedField P)ˣ := Finite.one_lt_card_iff_nontrivial.mp hbcard
  obtain ⟨b,hb⟩ := exists_ne (1 : (fixedField P)ˣ)
  have hb' : b.val.val≠1 := fun h => hb (Units.ext (Subtype.ext h))
  have hb2 : b.val.val^2≠1 := by
    let : CharP (ExtensionField P) 2 := inferInstance
    intro h
    exact hb' ((sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans (one_pow 2).symm)).elim id
      (fun h => h.trans (CharTwo.neg_eq 1)))
  let a : TorusCoordinates.OrbitParameters P := (TorusCoordinates.fixedUnit P b,b^2)
  let g := TorusCoordinates.torusMulEquiv P rfl a
  have hg := hc g ((torus_weyl_commute_iff P rfl a .arms).mpr (arms_torus_character P b))
  have hg' : FixedDescent.carrierToSplit P rfl g.val=
      TorusCoordinates.product P (TorusCoordinates.expand P a) := by
    change FixedDescent.carrierToSplit P rfl (TorusCoordinates.torusMulEquiv P rfl a).val=_
    rw [TorusCoordinates.torusMulEquiv_val P rfl a,FixedDescent.carrierToSplit_toCarrier P rfl]
    exact TorusCoordinates.inclusion_orbitElementary P rfl a
  have hconj : g.val*x*g.val⁻¹=x := by rw [hg.eq,mul_inv_cancel_right]
  have hh := congrArg (FixedDescent.carrierToSplit P rfl) hconj
  simp only [map_mul,map_inv,hg',hv] at hh
  rw [TrialityOuterTorus.product_orderedProduct P rfl] at hh
  have hz (j : Fin 12) (hj : 3≤j.val) : expand P v j=0 := by
    have he := congrFun (orderedProduct_injective P hh) j
    change TrialityOuterTorus.rootWeight P (TorusCoordinates.expand P a) j * expand P v j = _ at he
    rw [arms_fixed_weights] at he
    split_ifs at he with h h
    · omega
    · exact eq_zero_of_mul_eq_self_left hb2 he
    · exact eq_zero_of_mul_eq_self_left hb' (by simpa only [pow_one] using he)
  have h30 := hz 3 (by decide)
  have h41 := hz 4 (by decide)
  have h72 := hz 7 (by decide)
  have h101 := hz 10 (by decide)
  have h112 := hz 11 (by decide)
  have hzero : v.2 0=0 ∧ v.1 1=0 ∧ v.1 2=0 ∧ v.2 1=0 ∧ v.2 2=0 := by
    exact ⟨Subtype.ext h30,h41,h72,Subtype.ext h101,Subtype.ext h112⟩
  refine ⟨v.1 0,?_⟩
  apply FixedDescent.carrierToSplit_injective P rfl
  rw [hv]
  change _=FixedDescent.carrierToSplit P rfl (toCarrier P (ConcreteBruhat.rootElementary P rfl true .arms (v.1 0)))
  rw [FixedDescent.carrierToSplit_toCarrier P rfl]
  change orderedProduct P (expand P v)=foldedRoot P true (v.1 0)
  simp [orderedProduct,expand,List.ofFn_succ,hzero.1,hzero.2.1,hzero.2.2.1,
    hzero.2.2.2.1,hzero.2.2.2.2,foldedRoot,simpleRoot,←curve_simple,
    simplePosition,mul_assoc,-fieldFrobenius_apply]

private theorem torus_commute (P : Parameters) (hp : P.prime=2)
    (x y : torus P) : Commute x.val y.val := by
  obtain ⟨a,rfl⟩ := (TorusCoordinates.torusMulEquiv P hp).surjective x
  obtain ⟨b,rfl⟩ := (TorusCoordinates.torusMulEquiv P hp).surjective y
  exact congrArg Subtype.val ((map_mul _ a b).symm.trans
    ((congrArg (TorusCoordinates.torusMulEquiv P hp) (mul_comm a b)).trans (map_mul _ b a)))

private theorem fixed_torus_invariant {G : Type*} [Group G] [Finite G]
    (D : Subgroup G) (a : MulAut G) (hD : D.map a.toMonoidHom=D)
    (hc : ∀ x ∈ D, ∀ y ∈ D, Commute x y)
    (w : G) (d : D) (hw : a w=d.val*w) :
    (D ⊓ centralizer ({w} : Set G)).map a.toMonoidHom=D ⊓ centralizer ({w} : Set G) := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    have ha : a x∈D := hD ▸ mem_map_of_mem a.toMonoidHom hx.1
    refine ⟨ha,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg a (mem_centralizer_singleton_iff.mp hx.2)
    simp only [map_mul,hw] at hh
    change a x*w=w*a x
    apply mul_left_cancel (a := d.val)
    simpa only [←mul_assoc,(hc (a x) ha d d.property).eq] using hh
  · rw [card_map_of_injective a.injective]

private theorem positive_arms_preserved (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (b : MulAut (parabolic (binaryParameters n hn) .arms))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms))
    (hU : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (unipotent (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms))
    (r : ExtensionField (binaryParameters n hn)) :
    ∃ s : ExtensionField (binaryParameters n hn),
      (b ⟨rootElement (binaryParameters n hn) rfl true .arms r,
        borel_le_parabolic _ .arms (unipotent_le_borel _ (positive_mem_unipotent _ rfl .arms r))⟩).val =
          rootElement (binaryParameters n hn) rfl true .arms s := by
  let P := binaryParameters n hn
  let Q := parabolic P .arms
  let w : Q := ⟨simpleRepresentative P rfl .arms,simpleRepresentative_mem_parabolic P rfl .arms⟩
  let D := (torus P).subgroupOf Q
  let K := D ⊓ centralizer ({w} : Set Q)
  obtain ⟨d,hd⟩ := TrialityWeylAction.parabolic_aut_weyl n hn hn2 .arms b hD
  have hK : K.map b.toMonoidHom=K := fixed_torus_invariant D b hD
    (fun x hx y hy => Subtype.ext (torus_commute P rfl ⟨x.val,hx⟩ ⟨y.val,hy⟩).eq)
    w ⟨⟨d.val,(torus_le_borel P).trans (borel_le_parabolic P .arms) d.property⟩,d.property⟩
    (Subtype.ext hd)
  let x : Q := ⟨rootElement P rfl true .arms r,
    borel_le_parabolic P .arms (unipotent_le_borel P (positive_mem_unipotent P rfl .arms r))⟩
  apply arms_root_of_centralizes_fixed_torus n hn hn2 (b x).val
  · have hh := mem_map_of_mem b.toMonoidHom
      (show x∈(unipotent P).subgroupOf Q from positive_mem_unipotent P rfl .arms r)
    rw [hU] at hh
    exact hh
  · intro g hgw
    let gQ : Q := inclusion ((torus_le_borel P).trans (borel_le_parabolic P .arms)) g
    have hgK : gQ∈K := ⟨g.property,mem_centralizer_singleton_iff.mpr (Subtype.ext hgw.eq)⟩
    rw [←hK] at hgK
    obtain ⟨y,hy,hey⟩ := hgK
    have hyt : y.val∈torus P := hy.1
    obtain ⟨v,hv⟩ := (TorusCoordinates.torusMulEquiv P rfl).surjective ⟨y.val,hyt⟩
    have hvc : nodeCharacter P v .arms=1 :=
      (torus_weyl_commute_iff P rfl v .arms).mp (by
        rw [hv]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy.2))
    have hxy : Commute y x := by
      apply Subtype.ext
      apply mul_inv_eq_iff_eq_mul.mp
      change y.val*rootElement P rfl true .arms r*y.val⁻¹=rootElement P rfl true .arms r
      rw [←congrArg Subtype.val hv,torus_root_conjugate P rfl v true .arms r,hvc]
      simp [signedScalar]
    have he := congrArg Subtype.val (hxy.map b).eq
    change b y=gQ at hey
    rw [hey] at he
    exact he

private def armsRoot (P : Parameters) (hp : P.prime=2) (r : ExtensionField P) :
    parabolic P .arms :=
  ⟨rootElement P hp true .arms r,
    borel_le_parabolic P .arms (unipotent_le_borel P (positive_mem_unipotent P hp .arms r))⟩

private theorem armsRoot_injective (P : Parameters) (hp : P.prime=2) :
    Function.Injective (armsRoot P hp) := fun _ _ h =>
  rootElement_injective P hp true .arms (congrArg Subtype.val h)

private theorem armsRoot_add (P : Parameters) (hp : P.prime=2) (r s : ExtensionField P) :
    armsRoot P hp (r+s)=armsRoot P hp r*armsRoot P hp s :=
  Subtype.ext (rootElement_add P hp true .arms r s)

/-- A torus- and positive-subgroup-preserving arms parabolic automorphism
induces an additive equivalence on the literal cubic-field simple root. -/
theorem arms_root_action (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (b : MulAut (parabolic (binaryParameters n hn) .arms))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms))
    (hU : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (unipotent (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms)) :
    ∃ ρ : ExtensionField (binaryParameters n hn) ≃+ ExtensionField (binaryParameters n hn),
      ∀ r, (b ⟨rootElement (binaryParameters n hn) rfl true .arms r,
        borel_le_parabolic _ .arms (unipotent_le_borel _ (positive_mem_unipotent _ rfl .arms r))⟩).val =
          rootElement (binaryParameters n hn) rfl true .arms (ρ r) := by
  let P := binaryParameters n hn
  choose f hf using positive_arms_preserved n hn hn2 b hD hU
  have he (r) : b (armsRoot P rfl r)=armsRoot P rfl (f r) := Subtype.ext (hf r)
  have hi : Function.Injective f := by
    intro r s h
    apply armsRoot_injective P rfl
    apply b.injective
    rw [he,he,h]
  have hadd (r s) : f (r+s)=f r+f s := by
    apply armsRoot_injective P rfl
    rw [←he,armsRoot_add P rfl r s,map_mul,he,he,armsRoot_add P rfl (f r) (f s)]
  let fhom : ExtensionField P →+ ExtensionField P :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        exact (add_eq_left.mp (by simpa only [add_zero] using h.symm))
      map_add' := hadd }
  exact ⟨AddEquiv.ofBijective fhom ⟨hi,Finite.surjective_of_injective hi⟩,hf⟩

private theorem arms_root_mem_levi (P : Parameters) (hp : P.prime=2) (r : ExtensionField P) :
    rootElement P hp true .arms r ∈ levi P .arms := by
  refine ⟨ConcreteBruhat.rootElementary P hp true .arms r,?_,rfl⟩
  change foldedRoot P true r ∈ splitLevi P .arms
  have hmem (i : Fin 4) (hi : i≠1) (t : ExtensionField P) :
      positiveRoot P i t ∈ splitLevi P .arms :=
    subset_closure ⟨i,hi,t,Or.inl rfl⟩
  exact (splitLevi P .arms).mul_mem
    ((splitLevi P .arms).mul_mem (hmem 0 (by decide) r)
      (hmem 2 (by decide) (fieldFrobenius P r)))
    (hmem 3 (by decide) (fieldFrobenius P (fieldFrobenius P r)))

private theorem nonzero_fixed {F : Type*} [Field F] [CharP F 2]
    (ρ : F ≃+ F) (hρ : Function.Involutive ρ) : ∃ r : F, r≠0 ∧ ρ r=r := by
  by_cases h : ρ 1=1
  · exact ⟨1,one_ne_zero,h⟩
  · refine ⟨1+ρ 1,?_,?_⟩
    · intro hh
      exact h ((CharTwo.add_eq_zero.mp hh).symm)
    · rw [map_add,hρ]
      exact add_comm _ _

/-- Every involution with these genuine local markings fixes a nontrivial
cubic-field root element outside the arms radical. No fixed-lift premise is used. -/
theorem fixed_root_outside_radical (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (b : MulAut (parabolic (binaryParameters n hn) .arms))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms))
    (hU : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .arms)).map b.toMonoidHom =
        (unipotent (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .arms))
    (hb : Function.Involutive b) :
    ∃ x : parabolic (binaryParameters n hn) .arms,
      x.val∈unipotent (binaryParameters n hn) ∧ b x=x ∧
        x.val∉radical (binaryParameters n hn) .arms := by
  let P := binaryParameters n hn
  obtain ⟨ρ,hρ⟩ := arms_root_action n hn hn2 b hD hU
  have he (r) : b (armsRoot P rfl r)=armsRoot P rfl (ρ r) := Subtype.ext (hρ r)
  have hi : Function.Involutive ρ := by
    intro r
    apply armsRoot_injective P rfl
    rw [←he,←he,hb]
  obtain ⟨r,hr,hfix⟩ := nonzero_fixed ρ hi
  refine ⟨armsRoot P rfl r,positive_mem_unipotent P rfl .arms r,?_,?_⟩
  · rw [he,hfix]
  · intro hx
    have h1 := disjoint_def.mp (RadicalCoordinates.disjoint_radical_levi P rfl .arms)
      hx (arms_root_mem_levi P rfl r)
    have hz : rootElement P rfl true .arms (0 : ExtensionField P)=1 := by
      have hh := rootElement_add P rfl true .arms 0 0
      exact mul_left_cancel (by simpa only [add_zero,mul_one] using hh.symm)
    exact hr (rootElement_injective P rfl true .arms (h1.trans hz.symm))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityRootAction
