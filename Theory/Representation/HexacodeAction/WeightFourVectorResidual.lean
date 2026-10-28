module

public import Theory.Representation.HexacodeAction.WeightFourVectorStabilizer
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.SpecificGroups.SymmetricFourResidualCore
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The cubic residual moves the quotient at a weight-four point

The explicit word B²A fixes the weight-four vector with field coordinates
(0,0,1), has cube one, and acts on the quotient by its field point with
eigenvalues omega² and omega. An explicit displacement formula generates
the whole quotient. Conjugacy on the actual weight-four orbit transports
the formula to every weight-four vector.

Source: Aschbacher--Smith12.7.2(5),12.7.15(4), printed pp.839,843.
The actor is the literal two-residual of the vector stabilizer, so the
central scalar cubic in the setwise stabilizer is not substituted for it.
-/

public noncomputable section
open Atlas.Codes Subgroup Theory.GroupTheory
namespace Representation.Hexacode
open SixDimensional.EvenImage BinaryOffender

private theorem alternating_four_core_card :
    Nat.card (pCore 2 (alternatingGroup (Fin 4)))=4 := by
  rw [pCore_eq_comap_of_normal]
  change Nat.card ((pCore 2 (Equiv.Perm (Fin 4))).subgroupOf (alternatingGroup (Fin 4)))=4
  rw [Nat.card_congr (subgroupOfEquivOfLe (show pCore 2 (Equiv.Perm (Fin 4)) ≤
    alternatingGroup (Fin 4) from by
      rw [←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
      intro x hx
      exact Equiv.Perm.mem_alternatingGroup.mpr
        ((Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff x).mp hx).1)).toEquiv,
    ←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]

/-- The S4 marking sends the literal vector-stabilizer residual onto A4. -/
theorem weightFourVectorResidual_image (v : hexacode) (hv : hammingNorm v.val=4) :
    (pResidual 2 (fullWeightVectorStabilizer v)).map
      (weightFourVectorStabilizerEquiv v hv).toMonoidHom=alternatingGroup (Fin 4) := by
  rw [map_pResidual,Theory.SpecificGroups.SymmetricFourResidual.residual_eq]

/-- The actual vector stabilizer's two-residual has cyclic quotient of order
three by its intrinsic two-core. -/
theorem weightFourVectorResidual_quotient_card (v : hexacode)
    (hv : hammingNorm v.val=4) :
    Nat.card (pResidual 2 (fullWeightVectorStabilizer v) ⧸
      pCore 2 (pResidual 2 (fullWeightVectorStabilizer v)))=3 := by
  let e := weightFourVectorStabilizerEquiv v hv
  let er : pResidual 2 (fullWeightVectorStabilizer v) ≃* alternatingGroup (Fin 4) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
      change (pResidual 2 (fullWeightVectorStabilizer v)).map e.toMonoidHom = _
      exact weightFourVectorResidual_image v hv))
  rw [Nat.card_congr (QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).toEquiv]
  have hc := (pCore 2 (alternatingGroup (Fin 4))).card_mul_index
  rw [alternating_four_core_card,nat_card_alternatingGroup] at hc
  norm_num at hc
  change (pCore 2 (alternatingGroup (Fin 4))).index=3
  omega

private def seed : hexacode := ⟨systematicEncoder ![0,0,a],systematic_mem _⟩
private def cubic : HexEvenAutomorphisms := generatorB^2*generatorA

private theorem seed_coordinates : fieldCoordinates seed = ![0,0,1] := by
  funext i
  change orientedLetter (firstThree i) (seed.val (firstThree i)) = _
  revert i
  decide

private theorem seed_weight : hammingNorm seed.val = 4 := by decide

private theorem seed_ne_zero : seed ≠ 0 := by
  intro h
  have hh := seed_weight
  simp [h] at hh

private theorem cubic_three : cubic^3=1 := by
  calc
    cubic^3 = generatorB^2 * (generatorA*generatorB^2)^3 * (generatorB^2)⁻¹ := by
      dsimp [cubic]
      simp only [pow_succ,pow_zero]
      group
    _ = 1 := by rw [generatorAB2_three,mul_one,mul_inv_cancel]

private theorem cubic_coordinates (v : hexacode) :
    fieldCoordinates (evenAction cubic v) =
      ![omega^2*fieldCoordinates v 0,omega*fieldCoordinates v 1,
        fieldCoordinates v 0+fieldCoordinates v 1+fieldCoordinates v 2] := by
  have ha (u : hexacode) : fieldCoordinates (evenAction generatorA u)=
      ![fieldCoordinates u 0+fieldCoordinates u 1+fieldCoordinates u 2,
        fieldCoordinates u 0,fieldCoordinates u 1] := generatorA_coordinates u
  have hb (u : hexacode) : fieldCoordinates (evenAction generatorB u)=
      ![fieldCoordinates u 2,omega*fieldCoordinates u 0,omega^2*fieldCoordinates u 1] :=
    generatorB_coordinates u
  rw [cubic,map_mul,Module.End.mul_apply,pow_two,map_mul,Module.End.mul_apply,hb,hb,ha]
  have hh : ∀ x : Fin 3 → F,
      ![omega^2*(x 0),omega*(x 1),
        omega^2*(omega*(x 0+x 1+x 2))] =
      ![omega^2*x 0,omega*x 1,x 0+x 1+x 2] := by
    decide +kernel
  exact hh (fieldCoordinates v)

private theorem cubic_fixes_seed : evenAction cubic seed = seed := by
  apply fieldCoordinates.injective
  rw [cubic_coordinates,seed_coordinates]
  decide

private def input (x : Fin 3 → F) : Fin 3 → F := ![omega^2*x 0,omega*x 1,0]
private def coefficient (x : Fin 3 → F) : F := x 2+omega^2*x 0+omega*x 1

private theorem seed_decomposition (w : hexacode) :
    ∃ x : hexacode, ∃ r : F, w = (evenAction cubic x-x)+r•seed := by
  refine ⟨fieldCoordinates.symm (input (fieldCoordinates w)),coefficient (fieldCoordinates w),?_⟩
  apply fieldCoordinates.injective
  rw [map_add,map_sub,fieldCoordinates.map_smul,cubic_coordinates,
    fieldCoordinates.apply_symm_apply,seed_coordinates]
  have hh : ∀ y : Fin 3 → F,
      y = (![omega^2*(input y) 0,omega*(input y) 1,
        (input y) 0+(input y) 1+(input y) 2]-input y)+coefficient y•![0,0,1] := by
    decide +kernel
  exact hh (fieldCoordinates w)

/-- A single actual cubic fixes the weight-four vector and has surjective
displacement modulo its literal field point. -/
theorem weightFourVector_cubic_displacement (v : hexacode)
    (hv : hammingNorm v.val = 4) :
    ∃ g : HexEvenAutomorphisms, evenAction g v=v ∧ g^3=1 ∧
      ∀ w : hexacode, ∃ x : hexacode, ∃ r : F, w=(evenAction g x-x)+r•v := by
  have hv_mem : v ∈ Set.range (fun k : HexEvenAutomorphisms => evenAction k seed) := by
    rw [evenAction_orbit_eq_weight seed seed_ne_zero]
    exact hv.trans seed_weight.symm
  obtain ⟨k,rfl⟩ := hv_mem
  have hconj (g : HexEvenAutomorphisms) (u : hexacode) :
      evenAction (k*g*k⁻¹) (evenAction k u) = evenAction k (evenAction g u) := by
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  refine ⟨k*cubic*k⁻¹,?_,?_,?_⟩
  · rw [hconj,cubic_fixes_seed]
  · change (MulAut.conj k cubic)^3=1
    rw [←map_pow,cubic_three,map_one]
  · intro w
    obtain ⟨x,r,he⟩ := seed_decomposition (evenAction k⁻¹ w)
    refine ⟨evenAction k x,r,?_⟩
    have hh := congrArg (evenFieldAction k) he
    rw [map_add,map_sub,map_smul] at hh
    rw [hconj]
    have hk : evenFieldAction k (evenAction k⁻¹ w)=w := by
      change evenAction k (evenAction k⁻¹ w)=w
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    rw [hk] at hh
    have hbinary (g : HexEvenAutomorphisms) (u : hexacode) :
        evenFieldAction g u=evenAction g u := rfl
    simp only [hbinary] at hh
    exact hh

/-- The literal two-residual of the weight-four vector stabilizer generates
the whole quotient by the same scalar point. -/
theorem weightFourVectorResidual_commutator_sup_point (v : hexacode)
    (hv : hammingNorm v.val = 4) :
    subspaceCommutator evenAction ⊤
        ((pResidual 2 (fullWeightVectorStabilizer v)).map (fullWeightVectorStabilizer v).subtype) ⊔
      (Submodule.span F {v}).restrictScalars Bit = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨g,hg,hg3,hdisplace⟩ := weightFourVector_cubic_displacement v hv
  obtain ⟨x,r,rfl⟩ := hdisplace w
  have hgr : (⟨g,hg⟩ : fullWeightVectorStabilizer v) ∈
      pResidual 2 (fullWeightVectorStabilizer v) := by
    apply mem_pResidual_of_orderOf_coprime
    apply (by decide : Nat.Coprime 2 3).of_dvd_right
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hg3
  apply Submodule.add_mem
  · apply Submodule.mem_sup_left
    exact Submodule.subset_span ⟨g,mem_map_of_mem _ hgr,x,Submodule.mem_top,rfl⟩
  · exact Submodule.mem_sup_right (Submodule.mem_span_singleton.mpr ⟨r,rfl⟩)

end Representation.Hexacode
