module
public import Theory.Representation.SL2SylowFixedRecognition
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.ElementaryPerfectSplit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.FixedTransfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Recognition.Descent
/-!
# Natural coordinates on the literal opposite-core quotient

The original conjugation action on Q/((W∩Wʸ)V) descends through the marked
map I → SL₂(F). Its two complementary root fixed spaces are therefore
Sylow fixed spaces for these same matrix actors. The shared G.1.7 theorem
constructs natural coordinates; its G.1.6 hypotheses give fixed-space
uniformity for every nonidentity element of each opposite root.

The exported factor identities use the literal quotient projection.
The Cartan-compatible selection retains X₁≤I and the three L₁-conjugators,
and the fixed-point application removes the natural-coordinate premise
from the existing core transfer. Constructing the marked diagonal Cartan
element and proving conjugacy under O₂(I) remain with the opposite-core
assembly. No containment of Q in O₂(G₁) is assumed here.

Source: Aschbacher--Smith, G.1.6--7, printed pp.329--330, and 11.5.7,
printed p.783.
-/

open Subgroup Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
set_option backward.isDefEq.respectTransparency false
noncomputable section

private theorem exists_action_descent {H B M : Type*} [Group H] [Group B] [Group M]
    (f : H →* B) (hf : Function.Surjective f)
    (ρ : H →* MulAut M) (hk : f.ker ≤ ρ.ker) :
    ∃ σ : B →* MulAut M, ∀ h, σ (f h) = ρ h := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let σ := (QuotientGroup.lift f.ker ρ hk).comp e.symm.toMonoidHom
  refine ⟨σ,?_⟩
  intro h
  have he : e (QuotientGroup.mk' f.ker h) = f h := rfl
  change QuotientGroup.lift f.ker ρ hk (e.symm (f h)) = ρ h
  rw [← he,e.symm_apply_apply]
  rfl

private theorem fixedSpace_map_descent
    {H B M : Type*} [Group H] [Group B] [Group M] [IsElementaryAbelian 2 M]
    (f : H →* B) (ρ : H →* MulAut M) (σ : B →* MulAut M)
    (he : ∀ h, σ (f h) = ρ h) (U : Subgroup H) :
    fixedSpace (Representation.elementaryRepresentation (p := 2) σ) (U.map f) =
      fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) U := by
  ext v
  constructor
  · intro hv u
    have hh := hv ⟨f u,mem_map_of_mem f u.property⟩
    change Additive.ofMul (σ (f u) v.toMul) = v at hh
    rwa [he] at hh
  · intro hv a
    obtain ⟨u,hu,he'⟩ := a.property
    have hh := hv ⟨u,hu⟩
    change Additive.ofMul (σ a.val v.toMul) = v
    rw [← he',he]
    exact hh

private theorem fixed_factor_of_uniformity
    {H M : Type*} [Group H] [Group M] [IsElementaryAbelian 2 M]
    (ρ : H →* MulAut M) (U : Subgroup H) (i : H)
    (hu : fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) (zpowers i) =
      fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) U)
    (A : Subgroup M) (hA : ∀ v, (∀ j : H, j ∈ U → ρ j v = v) ↔ v ∈ A) :
    ∀ v, ρ i v = v ↔ v ∈ A := by
  intro v
  apply Iff.trans ?_ (hA v)
  constructor
  · intro hi j hj
    have hv := (mem_fixedSpace_zpowers_iff (Representation.elementaryRepresentation (p := 2) ρ)
      i (Additive.ofMul v)).mpr (congrArg Additive.ofMul hi)
    rw [hu] at hv
    exact congrArg Additive.toMul (hv ⟨j,hj⟩)
  · intro hv
    have hh : Additive.ofMul v ∈ fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) U :=
      fun j => congrArg Additive.ofMul (hv j j.property)
    rw [← hu] at hh
    exact congrArg Additive.toMul ((mem_fixedSpace_zpowers_iff _ _ _).mp hh)


private theorem natural_coordinates_of_root_descent
    {H F M : Type*} [Group H] [Field F] [Finite F] [CharP F 2]
    [Group M] [Finite M] [IsElementaryAbelian 2 M]
    (f : H →* SL(2,F)) (hf : Function.Surjective f)
    (ρ : H →* MulAut M) (hk : f.ker ≤ ρ.ker)
    (U : Subgroup H) (R : Sylow 2 SL(2,F)) (hU : U.map f = R)
    (j : H)
    (hcompl : IsCompl (fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) U)
      (fixedSpace (Representation.elementaryRepresentation (p := 2) ρ)
        (U.map (MulAut.conj j).toMonoidHom)))
    (d : ℕ) (hd : 2 ≤ d) (hF : Nat.card F = 2^d) :
    ∃ (σ : SL(2,F) →* MulAut M),
      (∀ h, σ (f h) = ρ h) ∧
      Representation.SL2SylowFixedRecognition.FixedSpaceHypotheses
        (Representation.elementaryRepresentation (p := 2) σ) R ∧
      (∀ u ∈ U, f u ≠ 1 →
        fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) (zpowers u) =
          fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) U) ∧
      (∀ u ∈ U.map (MulAut.conj j).toMonoidHom, f u ≠ 1 →
        fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) (zpowers u) =
          fixedSpace (Representation.elementaryRepresentation (p := 2) ρ)
            (U.map (MulAut.conj j).toMonoidHom)) ∧
      Representation.SL2SylowFixedRecognition.NaturalCoordinates
        (Representation.elementaryRepresentation (p := 2) σ) := by
  obtain ⟨σ,hσ⟩ := exists_action_descent f hf ρ hk
  let S := R.mapSurjective (f := (MulAut.conj (f j)).toMonoidHom) (MulAut.conj (f j)).surjective
  have hUS : (U.map (MulAut.conj j).toMonoidHom).map f = S := by
    change _ = (R : Subgroup SL(2,F)).map (MulAut.conj (f j)).toMonoidHom
    rw [← hU,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro u
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  have hc : IsCompl (fixedSpace (Representation.elementaryRepresentation (p := 2) σ) R)
      (fixedSpace (Representation.elementaryRepresentation (p := 2) σ) S) := by
    rw [← hU,← hUS,fixedSpace_map_descent f ρ σ hσ,
      fixedSpace_map_descent f ρ σ hσ]
    exact hcompl
  have hR := Representation.SL2SylowFixedRecognition.fixedSpaceHypotheses_of_isCompl _ R S hc
  have hS := Representation.SL2SylowFixedRecognition.fixedSpaceHypotheses_of_isCompl _ S R hc.symm
  have uniform (A : Subgroup H) (P : Sylow 2 SL(2,F)) (hAP : A.map f = P)
      (hP : Representation.SL2SylowFixedRecognition.FixedSpaceHypotheses
        (Representation.elementaryRepresentation (p := 2) σ) P) :
      ∀ u ∈ A, f u ≠ 1 →
        fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) (zpowers u) =
          fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) A := by
    intro u hu hu1
    rw [← fixedSpace_map_descent f ρ σ hσ,← fixedSpace_map_descent f ρ σ hσ,
      MonoidHom.map_zpowers,hAP]
    exact hP.uniform (f u) (hAP ▸ mem_map_of_mem f hu) hu1
  exact ⟨σ,hσ,hR,uniform U R hU hR,uniform _ S hUS hS,
    Representation.SL2SylowFixedRecognition.natural_of_complementary_sylow_fixed _ R S hc d hd hF⟩


public noncomputable section
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The literal quotient has natural matrix coordinates and the asserted
individual-root fixed factors, with no recognition or descent premise. -/
theorem exists_natural_quotient_coordinates
    (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = LocalGeometry.Sp4.ModelFlag.movedStage g 1)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hroot : actionImage (V := V) (auxiliaryW E) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hmove : ⁅V,auxiliaryW E⁆ = E.V₁)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj (y:G)).toMonoidHom)
    (hcore : (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 ≤ (L ⊔ (T:Subgroup G)).pCoreIn 2) :
    let I := oppositeJoin (auxiliaryW E) (y:G)
    let Q := corePair (auxiliaryW E) (y:G)
    let N := pairDenominator E (y:G)
    let _ := denominator_normal_in_corePair E m y.property hW hPhi
    let _ := quotient_elementary E m y.property hW hPhi hcore
    ∃ (ρ : I →* MulAut (Q ⧸ N.subgroupOf Q))
      (σ : SL(2,E.input.field.Carrier) →* MulAut (Q ⧸ N.subgroupOf Q)),
      (∀ i : I, ∀ q : Q, ∀ hq : (i:G)*(q:G)*(i:G)⁻¹ ∈ Q,
        ρ i (QuotientGroup.mk' (N.subgroupOf Q) q) =
          QuotientGroup.mk' (N.subgroupOf Q) ⟨(i:G)*(q:G)*(i:G)⁻¹,hq⟩) ∧
      (∀ i, σ (pairAction E m hW g y hi i) = ρ i) ∧
      Representation.SL2SylowFixedRecognition.FixedSpaceHypotheses
        (Representation.elementaryRepresentation (p := 2) σ)
        (Matrix.SpecialLinearGroup.upperUnipotentSylow E.input.field.Carrier 2) ∧
      (∀ i : I, (i:G) ∈ auxiliaryW E → pairAction E m hW g y hi i ≠ 1 →
        fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) (zpowers i) =
          fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) ((auxiliaryW E).subgroupOf I)) ∧
      (∀ i : I, (i:G) ∈ (auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom →
        pairAction E m hW g y hi i ≠ 1 →
        fixedSpace (Representation.elementaryRepresentation (p := 2) ρ) (zpowers i) =
          fixedSpace (Representation.elementaryRepresentation (p := 2) ρ)
            (((auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom).subgroupOf I)) ∧
      (∀ i : I, (i:G) ∈ auxiliaryW E → pairAction E m hW g y hi i ≠ 1 →
        ∀ u, ρ i u = u ↔ u ∈ (((auxiliaryW E ⊔ V) ⊓ Q).subgroupOf Q).map
          (QuotientGroup.mk' (N.subgroupOf Q))) ∧
      (∀ i : I, (i:G) ∈ (auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom →
        pairAction E m hW g y hi i ≠ 1 →
        ∀ u, ρ i u = u ↔ u ∈ ((((auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom ⊔ V) ⊓ Q).subgroupOf Q).map
          (QuotientGroup.mk' (N.subgroupOf Q))) ∧
      ∃ (s : ℕ) (e : Additive (Q ⧸ N.subgroupOf Q) ≃+ (Fin s → Fin 2 → E.input.field.Carrier)),
        ∀ i u k, e (Additive.ofMul (ρ i u)) k =
          Matrix.mulVec (pairAction E m hW g y hi i).val (e (Additive.ofMul u) k) := by
  dsimp only
  let : Algebra (ZMod 2) E.input.field.Carrier := ZMod.algebra _ 2
  let _ := denominator_normal_in_corePair E m y.property hW hPhi
  let _ := quotient_elementary E m y.property hW hPhi hcore
  obtain ⟨ρ,hρ,hcompl,_hz,_hgen⟩ := exists_binary_action_with_complementary_root_fixed_spaces
    E m hW hPhi g hpoint y hy hi hsplit hcore
  have hk := pairAction_kernel_trivial_on_quotient E m hW hPhi g hpoint y hy hi hroot hmove hcore ρ hρ
  let I := oppositeJoin (auxiliaryW E) (y:G)
  let U := (auxiliaryW E).subgroupOf I
  obtain ⟨j,hj,hjW⟩ := exists_inner_opposite_conjugator E m hW g hpoint y hy hi
  have hjU : U.map (MulAut.conj (⟨j,hj⟩ : I)).toMonoidHom =
      (((auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom).subgroupOf I) := by
    apply map_injective I.subtype_injective
    rw [map_map]
    have he : I.subtype.comp (MulAut.conj (⟨j,hj⟩ : I)).toMonoidHom =
        (MulAut.conj j).toMonoidHom.comp I.subtype := rfl
    rw [he,← map_map,map_subgroupOf_eq_of_le (show auxiliaryW E ≤ I from le_sup_left),
      map_subgroupOf_eq_of_le (show (auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom ≤ I from le_sup_right)]
    exact hjW
  obtain ⟨σ,hσ,hfixed,huniform,huniformZ,s,e,he⟩ := natural_coordinates_of_root_descent
    (pairAction E m hW g y hi) (pairAction_surjective E m hW g y hi) ρ hk U
    (Matrix.SpecialLinearGroup.upperUnipotentSylow E.input.field.Carrier 2)
    (pairAction_root E m hW g y hi hroot) ⟨j,hj⟩ (hjU.symm ▸ hcompl)
    E.input.field.degree E.input.nonbinary E.input.field.card_eq
  rw [hjU] at huniformZ
  have hf := quotient_fixed_factors_of_inner_conjugator E m y.property hW hPhi hsplit hcore
    ⟨j,hj⟩ hjW ρ hρ
  refine ⟨ρ,σ,hρ,hσ,hfixed,huniform,huniformZ,
    (fun i hi hn => fixed_factor_of_uniformity ρ U i (huniform i hi hn) _ hf.2.1),
    (fun i hi hn => fixed_factor_of_uniformity ρ _ i (huniformZ i hi hn) _ hf.2.2),
    s,e.toAddEquiv,?_⟩
  intro i u k
  have hh := he (pairAction E m hW g y hi i) (Additive.ofMul u) k
  change e (Additive.ofMul (σ (pairAction E m hW g y hi i) u)) k = _ at hh
  rw [hσ] at hh
  exact hh


/-- Discharge the natural-coordinate premise of the actual Cartan fixed-point
bound. The diagonal element still belongs to the torus construction. -/
theorem centralizer_le_of_marked_pair_diagonal
    (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = LocalGeometry.Sp4.ModelFlag.movedStage g 1)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hroot : actionImage (V := V) (auxiliaryW E) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hmove : ⁅V,auxiliaryW E⁆ = E.V₁)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj (y:G)).toMonoidHom)
    (hcore : (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 ≤ (L ⊔ (T:Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y:G))
    (x : G) (hx : x ∈ cartanKernel E) (t : E.input.field.Carrier) (ht : t ≠ 1)
    (hdiag : (pairAction E m hW g y hi ⟨x,hXI hx⟩).val = Matrix.diagonal ![t,t⁻¹]) :
    corePair (auxiliaryW E) (y:G) ⊓ centralizer (cartanKernel E : Set G) ≤ pairDenominator E (y:G) := by
  obtain ⟨ρ,σ,hρ,_hσ,_hfixed,_hU,_hZ,_hA,_hB,s,e,he⟩ := exists_natural_quotient_coordinates
    E m hW hPhi g hpoint y hy hi hroot hmove hsplit hcore
  exact centralizer_le_of_natural_coordinates E m y.property hW hPhi hcore hXI s
    ρ hρ (pairAction E m hW g y hi) e he x hx t ht hdiag


/-- Apply recognition to the actual Cartan-compatible opposite choice.
The quotient projection and matrix actors belong to the same selected y. -/
theorem exists_cartan_opposite_natural_coordinates
    (m : MarkedFlag E) (hX : LocalGeometry.IsCartan T L E.X)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hmove : ⁅V,auxiliaryW E⁆ = E.V₁)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁) :
    ∃ (g : Sp E.input.field.Carrier) (y : L)
      (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
      (hcore : (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 ≤ (L ⊔ (T:Subgroup G)).pCoreIn 2),
      (∀ k : Fin 3, m.flag.space k = LocalGeometry.Sp4.ModelFlag.movedStage g k.succ) ∧
      PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom ∧
      PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹ ∧
      cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y:G) ∧
      E.X ≤ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G) ∧
      V = E.V₃ ⊔ E.V₁.map (MulAut.conj (y:G)).toMonoidHom ∧
      (∃ l : Fin 3 → G, (∀ k, l k ∈ E.L₁) ∧
        L ≤ (⨆ k, (oppositeJoin (auxiliaryW E) (y:G)).map
          (MulAut.conj (l k)).toMonoidHom) ⊔ (L ⊔ (T:Subgroup G)).pCoreIn 2) ∧
      let I := oppositeJoin (auxiliaryW E) (y:G)
      let Q := corePair (auxiliaryW E) (y:G)
      let N := pairDenominator E (y:G)
      let _ := denominator_normal_in_corePair E m y.property hW hPhi
      let _ := quotient_elementary E m y.property hW hPhi hcore
      ∃ (s : ℕ) (e : Additive (Q ⧸ N.subgroupOf Q) ≃+ (Fin s → Fin 2 → E.input.field.Carrier)),
        ∀ (i : I) (q : Q) (hq : (i:G)*(q:G)*(i:G)⁻¹ ∈ Q) k,
          e (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf Q)
            ⟨(i:G)*(q:G)*(i:G)⁻¹,hq⟩)) k =
          Matrix.mulVec (pairAction E m hW g y hi i).val
            (e (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf Q) q)) k) := by
  obtain ⟨g,y,hflag,hlocal,hy,hi,hXI,hXp,_hXQ,_hs,hjoin,_hmeet,hcore,_hN,hgen⟩ :=
    OppositeGeometry.exists_cartan_opposite_with_kernel E m hX hW hroot hPhi
  have hr := hroot.trans (FullAction.center_eq_marked_root m g hlocal)
  obtain ⟨ρ,σ,hρ,_hσ,_hfixed,_hU,_hZ,_hA,_hB,s,e,he⟩ := exists_natural_quotient_coordinates
    E m hW hPhi g (hflag 0) y hy hi hr hmove hjoin.symm hcore
  refine ⟨g,y,hi,hcore,hflag,hlocal,hy,hXI,hXp,hjoin.symm,hgen,s,e,?_⟩
  intro i q hq k
  rw [← hρ i q hq]
  exact he i _ k

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
