module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLocalParametersModel
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLocalParametersModel
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootActionModel
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterTorus
import all Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity.Torus
import all Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity.Compatibility

/-!
# The central triality roots and compatibility of the two field coefficients

A torus element with trivial central-root character separates every other
positive root, including at q=4. Its positive-subgroup centralizer is exactly
the central simple root. Thus a torus- and positive-subgroup-preserving
central-parabolic automorphism preserves that root. The rank-one relations
then give reciprocal scalar-semilinear formulas on both signed central roots.

For two parabolic automorphisms agreeing on the literal Borel, conjugation by
the central coroot identifies the base-field coefficient with the restriction
of the cubic coefficient. Neither action is assumed to extend to the full
triality carrier. The companion source module applies these calculations
through both original compatible parabolic maps.

Source: GLS3 §§2.4--2.6, Steinberg Theorems 30(2),(4) and 36
(`refs/KGroup/GLS3/Chapter2St1.tex`); Aschbacher--Smith F.4.37--38 and 5.3.3
(`refs/quasithin.pdf`). Internal imports reuse the root and rank-one
calculations within the triality source family without changing their APIs.
-/

public noncomputable section
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.PositiveCoordinates
open Triality.Standard.Parabolics.RankOneMatrices Triality.Standard.ElementaryCentralKernel
open Triality.Standard.OuterOdd.Coverage.ParameterRigidity
open Triality.Standard.CentralCovers.TwoPrimary
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCentralAction
private def weights (F : Type*) [Field F] (u v w z : F) : Fin 12 → F :=
  ![u,v,w,z,u*z,v*z,w*z,u*v*z,v*w*z,u*w*z,u*v*w*z,u*v*w*z^2]
private theorem root_weights (P : Parameters) (a : TorusCoordinates.OrbitParameters P)
    (j : Fin 12) :
    TrialityOuterTorus.rootWeight P (TorusCoordinates.expand P a) j =
      weights (ExtensionField P) (splitCharacter P a 0) (splitCharacter P a 2)
        (splitCharacter P a 3) (splitCharacter P a 1) j := by
  have h0 := a.1.ne_zero
  have h2 : fieldFrobenius P a.1.val ≠ 0 := (map_ne_zero (fieldFrobenius P)).mpr h0
  have h3 : fieldFrobenius P (fieldFrobenius P a.1.val) ≠ 0 := (map_ne_zero (fieldFrobenius P)).mpr h2
  have h1 : a.2.val.val ≠ 0 := fun h => a.2.ne_zero (Subtype.ext h)
  fin_cases j <;>
    simp only [TrialityOuterTorus.rootWeight, TrialityOuterTorus.root_pairing,
      TrialityOuterTorus.pairing,TorusCoordinates.expand,weights,splitCharacter,
      Theory.AlgebraicGroup.StandardRootSystem.typeDCartanMatrix,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] <;>
    simp [TorusCoordinates.frobenius,TorusCoordinates.fixedUnit] <;> field_simp

private def degrees (q : ℕ) : Fin 12 → ℕ :=
  ![1,q,q^2,0,1,q,q^2,1+q,q+q^2,1+q^2,1+q+q^2,1+q+q^2]

private theorem character_weights (P : Parameters) (a : TorusCoordinates.OrbitParameters P)
    (u : (ExtensionField P)ˣ) (ha : rootCharacters P a=(u,1)) (j : Fin 12) :
    TrialityOuterTorus.rootWeight P (TorusCoordinates.expand P a) j=u.val^(degrees P.q j) := by
  have hc : nodeCharacter P a .central=1 := congrArg Prod.snd ha
  have hu : nodeCharacter P a .arms=u := congrArg Prod.fst ha
  rw [root_weights,splitCharacter_zero,splitCharacter_one,splitCharacter_two,splitCharacter_three,hc,hu]
  fin_cases j <;> simp [weights,degrees,fieldFrobenius_apply,pow_add,pow_two,pow_mul]

private theorem degrees_small (q : ℕ) (hq : 2<q) (j : Fin 12) (hj : j≠3) :
    0<degrees q j ∧ degrees q j<q^3-1 := by
  have hh : q^2+q+1<q^3-1 := by
    have h1 : 3≤q := hq
    have h2 : 9≤q^2 := by nlinarith
    have h3 : q^3=q*q^2 := by ring
    have hmul := Nat.mul_le_mul_right (q^2) h1
    have hsq : q≤q^2 := by nlinarith
    omega
  have hpos : 0<q^2 := pow_pos (by omega) _
  fin_cases j <;> first | exact False.elim (hj rfl) | (norm_num [degrees]; omega)

private theorem central_separating_torus (P : Parameters) (hp : P.prime=2) (hq : 2<P.q) :
    ∃ a : TorusCoordinates.OrbitParameters P, nodeCharacter P a .central=1 ∧
      ∀ j : Fin 12, j≠3 → TrialityOuterTorus.rootWeight P (TorusCoordinates.expand P a) j≠1 := by
  obtain ⟨u,hu⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := (ExtensionField P)ˣ)).mp inferInstance
  rw [Nat.card_units,card_extensionField] at hu
  obtain ⟨a,ha⟩ := rootCharacters_surjective P hp (u,1)
  refine ⟨a,congrArg Prod.snd ha,?_⟩
  intro j hj he
  rw [character_weights P a u ha j] at he
  have he' : u^(degrees P.q j)=1 := Units.ext he
  have hd := orderOf_dvd_of_pow_eq_one he'
  rw [hu] at hd
  have hb := degrees_small P.q hq j hj
  exact (Nat.not_le_of_gt hb.2) (Nat.le_of_dvd hb.1 hd)
private theorem central_root_of_centralizes_fixed_torus (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (x : Carrier (binaryParameters n hn)) (hx : x∈unipotent (binaryParameters n hn))
    (hc : ∀ g : torus (binaryParameters n hn),
      Commute g.val (simpleRepresentative (binaryParameters n hn) rfl .central) → Commute g.val x) :
    ∃ r : fixedField (binaryParameters n hn),
      x=rootElement (binaryParameters n hn) rfl true .central r := by
  let P := binaryParameters n hn
  let v := (positiveEquiv n hn).symm ⟨x,hx⟩
  have hv : FixedDescent.carrierToSplit P rfl x=orderedProduct P (expand P v) := by
    rw [←baseProduct_toSplit]
    apply congrArg (FixedDescent.carrierToSplit P rfl)
    exact (congrArg Subtype.val ((positiveEquiv n hn).apply_symm_apply ⟨x,hx⟩)).symm.trans
      (positiveEquiv_val n hn v)
  have hq : 2<P.q := Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) hn2
  obtain ⟨a,ha,hsep⟩ := central_separating_torus P rfl hq
  let g := TorusCoordinates.torusMulEquiv P rfl a
  have hg := hc g ((TrialityRootAction.torus_weyl_commute_iff P rfl a .central).mpr ha)
  have hg' : FixedDescent.carrierToSplit P rfl g.val=
      TorusCoordinates.product P (TorusCoordinates.expand P a) := by
    change FixedDescent.carrierToSplit P rfl (TorusCoordinates.torusMulEquiv P rfl a).val=_
    rw [TorusCoordinates.torusMulEquiv_val P rfl a,FixedDescent.carrierToSplit_toCarrier P rfl]
    exact TorusCoordinates.inclusion_orbitElementary P rfl a
  have hconj : g.val*x*g.val⁻¹=x := by rw [hg.eq,mul_inv_cancel_right]
  have hh := congrArg (FixedDescent.carrierToSplit P rfl) hconj
  simp only [map_mul,map_inv,hg',hv] at hh
  rw [TrialityOuterTorus.product_orderedProduct P rfl] at hh
  have hz (j : Fin 12) (hj : j≠3) : expand P v j=0 := by
    have he := congrFun (orderedProduct_injective P hh) j
    exact eq_zero_of_mul_eq_self_left (hsep j hj) he
  have hzero : v.1 0=0 ∧ v.1 1=0 ∧ v.1 2=0 ∧ v.2 1=0 ∧ v.2 2=0 :=
    ⟨hz 0 (by decide),hz 4 (by decide),hz 7 (by decide),
      Subtype.ext (hz 10 (by decide)),Subtype.ext (hz 11 (by decide))⟩
  refine ⟨v.2 0,?_⟩
  apply FixedDescent.carrierToSplit_injective P rfl
  rw [hv]
  change _=FixedDescent.carrierToSplit P rfl (toCarrier P (ConcreteBruhat.rootElementary P rfl true .central (v.2 0)))
  rw [FixedDescent.carrierToSplit_toCarrier P rfl]
  change orderedProduct P (expand P v)=simpleRoot P true 1 (v.2 0).val
  simp [orderedProduct,expand,List.ofFn_succ,hzero.1,hzero.2.1,hzero.2.2.1,
    hzero.2.2.2.1,hzero.2.2.2.2,simpleRoot,←curve_simple,
    simplePosition,-fieldFrobenius_apply]

private theorem positive_central_preserved (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (b : MulAut (parabolic (binaryParameters n hn) .central))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .central)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .central))
    (hU : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .central)).map b.toMonoidHom =
        (unipotent (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .central))
    (r : fixedField (binaryParameters n hn)) :
    ∃ s : fixedField (binaryParameters n hn),
      (b ⟨rootElement (binaryParameters n hn) rfl true .central r,
        borel_le_parabolic _ .central (unipotent_le_borel _ (positive_mem_unipotent _ rfl .central r))⟩).val =
          rootElement (binaryParameters n hn) rfl true .central s := by
  let P := binaryParameters n hn
  let Q := parabolic P .central
  let w : Q := ⟨simpleRepresentative P rfl .central,simpleRepresentative_mem_parabolic P rfl .central⟩
  let D := (torus P).subgroupOf Q
  let K := D ⊓ centralizer ({w} : Set Q)
  obtain ⟨d,hd⟩ := TrialityWeylAction.parabolic_aut_weyl n hn hn2 .central b hD
  have hK : K.map b.toMonoidHom=K := TrialityRootAction.fixed_torus_invariant D b hD
    (fun x hx y hy => Subtype.ext (TrialityRootAction.torus_commute P rfl ⟨x.val,hx⟩ ⟨y.val,hy⟩).eq)
    w ⟨⟨d.val,(torus_le_borel P).trans (borel_le_parabolic P .central) d.property⟩,d.property⟩
    (Subtype.ext hd)
  let x : Q := ⟨rootElement P rfl true .central r,
    borel_le_parabolic P .central (unipotent_le_borel P (positive_mem_unipotent P rfl .central r))⟩
  apply central_root_of_centralizes_fixed_torus n hn hn2 (b x).val
  · have hh := mem_map_of_mem b.toMonoidHom
      (show x∈(unipotent P).subgroupOf Q from positive_mem_unipotent P rfl .central r)
    rw [hU] at hh
    exact hh
  · intro g hgw
    let gQ : Q := inclusion ((torus_le_borel P).trans (borel_le_parabolic P .central)) g
    have hgK : gQ∈K := ⟨g.property,mem_centralizer_singleton_iff.mpr (Subtype.ext hgw.eq)⟩
    rw [←hK] at hgK
    obtain ⟨y,hy,hey⟩ := hgK
    have hyt : y.val∈torus P := hy.1
    obtain ⟨v,hv⟩ := (TorusCoordinates.torusMulEquiv P rfl).surjective ⟨y.val,hyt⟩
    have hvc : nodeCharacter P v .central=1 :=
      (TrialityRootAction.torus_weyl_commute_iff P rfl v .central).mp (by
        rw [hv]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy.2))
    have hxy : Commute y x := by
      apply Subtype.ext
      apply mul_inv_eq_iff_eq_mul.mp
      change y.val*rootElement P rfl true .central r*y.val⁻¹=rootElement P rfl true .central r
      rw [←congrArg Subtype.val hv,torus_root_conjugate P rfl v true .central r,hvc]
      simp [signedScalar]
    have he := congrArg Subtype.val (hxy.map b).eq
    change b y=gQ at hey
    rw [hey] at he
    exact he

private def centralRoot (P : Parameters) (hp : P.prime=2) (r : fixedField P) :
    parabolic P .central :=
  ⟨rootElement P hp true .central r,
    borel_le_parabolic P .central (unipotent_le_borel P (positive_mem_unipotent P hp .central r))⟩

private theorem centralRoot_injective (P : Parameters) (hp : P.prime=2) :
    Function.Injective (centralRoot P hp) := fun _ _ h =>
  rootElement_injective P hp true .central (congrArg Subtype.val h)

private theorem centralRoot_add (P : Parameters) (hp : P.prime=2) (r s : fixedField P) :
    centralRoot P hp (r+s)=centralRoot P hp r*centralRoot P hp s :=
  Subtype.ext (rootElement_add P hp true .central r s)

/-- A torus- and positive-subgroup-preserving central parabolic automorphism
induces an additive equivalence on the literal base-field simple root. -/
theorem central_root_action (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (b : MulAut (parabolic (binaryParameters n hn) .central))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .central)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .central))
    (hU : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .central)).map b.toMonoidHom =
        (unipotent (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .central)) :
    ∃ ρ : fixedField (binaryParameters n hn) ≃+ fixedField (binaryParameters n hn),
      ∀ r, (b ⟨rootElement (binaryParameters n hn) rfl true .central r,
        borel_le_parabolic _ .central (unipotent_le_borel _ (positive_mem_unipotent _ rfl .central r))⟩).val =
          rootElement (binaryParameters n hn) rfl true .central (ρ r) := by
  let P := binaryParameters n hn
  choose f hf using positive_central_preserved n hn hn2 b hD hU
  have he (r) : b (centralRoot P rfl r)=centralRoot P rfl (f r) := Subtype.ext (hf r)
  have hi : Function.Injective f := by
    intro r s h
    apply centralRoot_injective P rfl
    apply b.injective
    rw [he,he,h]
  have hadd (r s) : f (r+s)=f r+f s := by
    apply centralRoot_injective P rfl
    rw [←he,centralRoot_add P rfl r s,map_mul,he,he,centralRoot_add P rfl (f r) (f s)]
  let fhom : fixedField P →+ fixedField P :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        exact (add_eq_left.mp (by simpa only [add_zero] using h.symm))
      map_add' := hadd }
  exact ⟨AddEquiv.ofBijective fhom ⟨hi,Finite.surjective_of_injective hi⟩,hf⟩

/-- The two signed base-field roots have reciprocal scalars and the same field map. -/
theorem central_signed_field_action (n : ℕ) (hn : 0<n) (hn2 : 1<n)
    (b : MulAut (parabolic (binaryParameters n hn) .central))
    (hD : ((torus (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .central)).map b.toMonoidHom =
        (torus (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .central))
    (hU : ((unipotent (binaryParameters n hn)).subgroupOf
      (parabolic (binaryParameters n hn) .central)).map b.toMonoidHom =
        (unipotent (binaryParameters n hn)).subgroupOf (parabolic (binaryParameters n hn) .central)) :
    ∃ (c : (fixedField (binaryParameters n hn))ˣ)
      (σ : fixedField (binaryParameters n hn) ≃+* fixedField (binaryParameters n hn)),
      ∀ s r, b (TrialityLocalParameters.rootInParabolic (binaryParameters n hn) rfl s .central r)=
        TrialityLocalParameters.rootInParabolic (binaryParameters n hn) rfl s .central (signedScalar s c.val * σ r) := by
  let P := binaryParameters n hn
  obtain ⟨u,hu⟩ := central_root_action n hn hn2 b hD hU
  have hu' (r) : b (TrialityLocalParameters.rootInParabolic P rfl true .central r)=TrialityLocalParameters.rootInParabolic P rfl true .central (u r) :=
    Subtype.ext (hu r)
  obtain ⟨v,hv⟩ := TrialityLocalParameters.negative_action_of_positive n hn hn2 .central b hD u hu'
  have hp (r) : b (TrialityLocalParameters.rankOneLocal P rfl .central (upper r))=TrialityLocalParameters.rankOneLocal P rfl .central (upper (u r)) := by
    change b (TrialityLocalParameters.rankOneLocal P rfl .central (signed true r))=TrialityLocalParameters.rankOneLocal P rfl .central (signed true (u r))
    rw [TrialityLocalParameters.rankOneLocal_signed P rfl true .central r,TrialityLocalParameters.rankOneLocal_signed P rfl true .central (u r)]
    exact hu' r
  have hn' (r) : b (TrialityLocalParameters.rankOneLocal P rfl .central (lower r))=TrialityLocalParameters.rankOneLocal P rfl .central (lower (v r)) := by
    change b (TrialityLocalParameters.rankOneLocal P rfl .central (signed false r))=TrialityLocalParameters.rankOneLocal P rfl .central (signed false (v r))
    rw [TrialityLocalParameters.rankOneLocal_signed P rfl false .central r,TrialityLocalParameters.rankOneLocal_signed P rfl false .central (v r)]
    exact hv r
  obtain ⟨c,σ,hp',hn'⟩ := exists_rankOne_field (TrialityLocalParameters.rankOneLocal P rfl .central)
    (fun _ _ h => rankOne_injective P rfl .central (congrArg Subtype.val h)) b u v hp hn'
  refine ⟨c,σ,?_⟩
  intro s r
  cases s
  · simpa only [signedScalar,Bool.false_eq_true,if_false,hn' r] using hv r
  · simpa only [signedScalar,if_true,hp' r] using hu' r



open TrialityLocalParameters
open Triality.Standard.OuterOdd.Coverage
open TorusCoordinates Triality.Standard.OuterOdd

private def corootLocal (P : Parameters) (hp : P.prime=2) (i : Node)
    (v : (RootField P i)ˣ) : parabolic P i :=
  rankOneLocal P hp i (weyl v.val * weyl 1)

private theorem corootLocal_val (P : Parameters) (hp : P.prime=2) (i : Node)
    (v : (RootField P i)ˣ) : (corootLocal P hp i v).val=nodeTorus P hp i v :=
  (nodeTorus_eq_rankOne P hp i v).symm

private theorem corootLocal_action (P : Parameters) (hp : P.prime=2) (i : Node)
    (a : MulAut (parabolic P i)) (c : (RootField P i)ˣ)
    (σ : RootField P i ≃+* RootField P i)
    (ha : ∀ s r, a (rootInParabolic P hp s i r)=
      rootInParabolic P hp s i (signedScalar s c.val*σ r))
    (v : (RootField P i)ˣ) :
    a (corootLocal P hp i v)=corootLocal P hp i (Units.map σ.toMonoidHom v) := by
  let := rootField_charTwo P hp i
  have hu (r) : a (rankOneLocal P hp i (upper r))=
      rankOneLocal P hp i (upper (c.val*σ r)) := by
    change a (rankOneLocal P hp i (signed true r))=rankOneLocal P hp i (signed true (c.val*σ r))
    simpa only [rankOneLocal_signed,signedScalar,if_true] using ha true r
  have hl (r) : a (rankOneLocal P hp i (lower r))=
      rankOneLocal P hp i (lower (c.val⁻¹*σ r)) := by
    change a (rankOneLocal P hp i (signed false r))=rankOneLocal P hp i (signed false (c.val⁻¹*σ r))
    simpa only [rankOneLocal_signed,signedScalar,Bool.false_eq_true,if_false] using ha false r
  have hw (r) : a (rankOneLocal P hp i (weyl r))=rankOneLocal P hp i (weyl (c.val*σ r)) := by
    simp only [weyl,map_mul,hu,hl,map_inv₀,_root_.mul_inv_rev]
    rw [mul_comm (c.val⁻¹)]
  change a (rankOneLocal P hp i (weyl v.val*weyl 1))=rankOneLocal P hp i (weyl (σ v.val)*weyl 1)
  rw [map_mul,map_mul,hw,hw,map_one,mul_one,←map_mul]
  exact congrArg (rankOneLocal P hp i) (weyl_scaled c.val (σ v.val) c.ne_zero
    (by exact σ.injective.ne v.ne_zero |>.trans_eq (map_zero σ)))

private def centralCorootBorel (P : Parameters) (hp : P.prime=2)
    (v : (fixedField P)ˣ) : borel P :=
  ⟨nodeTorus P hp .central v, torus_le_borel P ⟨foldedTorusElementary P hp .central v,by
    change elementaryInclusion P _ ∈ splitTorus P
    rw [inclusion_foldedTorus_central]
    exact subset_closure ⟨1,TorusCoordinates.fixedUnit P v,rfl⟩,rfl⟩⟩

/-- Agreement on the literal Borel identifies the two root-field maps, without
extending either parabolic automorphism to the full triality carrier. -/
theorem fields_compatible_of_local_actions (P : Parameters) (hp : P.prime=2)
    (a : MulAut (parabolic P .central)) (b : MulAut (parabolic P .arms))
    (hB : ∀ x : borel P,
      (a (inclusion (borel_le_parabolic P .central) x)).val=
        (b (inclusion (borel_le_parabolic P .arms) x)).val)
    (c : (fixedField P)ˣ) (τ : fixedField P ≃+* fixedField P)
    (d : (ExtensionField P)ˣ) (σ : CoefficientAut P)
    (ha : ∀ s r, a (rootInParabolic P hp s .central r)=
      rootInParabolic P hp s .central (signedScalar s c.val*τ r))
    (hb : ∀ s r, b (rootInParabolic P hp s .arms r)=
      rootInParabolic P hp s .arms (signedScalar s d.val*σ r)) :
    coefficientFixedField P σ=τ := by
  let z (v : (fixedField P)ˣ) : parabolic P .arms :=
    inclusion (borel_le_parabolic P .arms) (centralCorootBorel P hp v)
  have hz (v : (fixedField P)ˣ) : b (z v)=z (Units.map τ.toMonoidHom v) := by
    apply Subtype.ext
    have he : inclusion (borel_le_parabolic P .central) (centralCorootBorel P hp v)=
        corootLocal P hp .central v := Subtype.ext (corootLocal_val P hp .central v).symm
    exact ((hB (centralCorootBorel P hp v)).symm.trans (congrArg (fun x => (a x).val) he)).trans
      ((congrArg Subtype.val (corootLocal_action P hp .central a c τ ha v)).trans
        (corootLocal_val P hp .central _))
  have hr (v : (fixedField P)ˣ) (r : ExtensionField P) :
      z v*rootInParabolic P hp true .arms r*(z v)⁻¹=
        rootInParabolic P hp true .arms (v.val.val⁻¹*r) :=
    Subtype.ext (centralTorus_arms P hp v r)
  apply RingEquiv.ext
  intro r
  apply Subtype.ext
  change σ r.val=(τ r).val
  by_cases hr0 : r=0
  · simp [hr0]
  let v : (fixedField P)ˣ := (Units.mk0 r hr0)⁻¹
  have hv : v.val.val⁻¹=r.val := by simp [v]
  have hh := congrArg b (hr v 1)
  simp only [map_mul,map_inv,hz,hb,signedScalar,if_true,map_one,mul_one] at hh
  rw [hr,hv] at hh
  have he := rootElement_injective P hp true .arms (congrArg Subtype.val hh)
  have hvτ : (Units.map τ.toMonoidHom v).val.val⁻¹=(τ r).val := by
    simp [v,-fieldFrobenius_apply]
  rw [hvτ,mul_comm] at he
  exact mul_left_cancel₀ d.ne_zero he.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCentralAction
