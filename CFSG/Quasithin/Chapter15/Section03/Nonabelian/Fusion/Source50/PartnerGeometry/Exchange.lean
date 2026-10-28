module
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PlaneGeometry
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.FactorPermutation
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.ExchangeObstruction

/-!
# The factor-exchanging source element and its two orbit planes

The actual factor interchange preserves the point and carries the first
residual orbit plane to the second. The two marked cubic orbits span exactly
the point-perpendicular hyperplane. This supplies the same outside element
and transverse seed used in 15.3.56(5–7).
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open ClassicalOrthogonal.FourPlusMatrix
open Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

abbrev rightResidual (d : Hypothesis D g) : Subgroup G := oddFactor
  (moduleProjection d.quotientSymmetricEquiv) D.L ProductDecomposition.rightFactor

theorem residual_exchange_of_factor_exchange (d : Hypothesis D g) (t : G)
    (ht : t ∈ D.T)
    (he : conjugate (factorPreimage d.quotientSymmetricEquiv
      ProductDecomposition.leftFactor) t =
      factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor) :
    conjugate (leftResidual d) t = rightResidual d := by
  have hL : D.L.map (MulAut.conj t⁻¹).toMonoidHom = D.L :=
    mem_normalizer_iff_map_conj_eq.mp (d.base.T_normalizes_L (D.T.inv_mem ht))
  unfold leftResidual rightResidual oddFactor conjugate
  rw [map_embedded_pResidual, map_inf _ _ _ (MulAut.conj t⁻¹).injective, hL]
  rw [show (actorPreimage (moduleProjection d.quotientSymmetricEquiv)
    ProductDecomposition.leftFactor).map (MulAut.conj t⁻¹).toMonoidHom =
      factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor from he]
  rfl

theorem orbit_plane_exchange (d : Hypothesis D g) (t : G) (ht : t ∈ D.T)
    (he : conjugate (leftResidual d) t = rightResidual d) :
    conjugate (localSpan D.V₁ (leftResidual d)) t =
      localSpan D.V₁ (rightResidual d) := by
  have hZ : conjugate D.V₁ t = D.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp (d.base.T_normalizes_point (D.T.inv_mem ht))
  change (conjugateSpanBy D.V₁ (leftResidual d)).map _ = _
  rw [map_conjugateSpanBy]
  change localSpan (conjugate D.V₁ t) (conjugate (leftResidual d) t) = _
  rw [hZ,he]

private def rightCubic : PairSL (F := ZMod 2) := (1, MatrixOrbit.cubic)

private theorem exists_right_cubic (d : Hypothesis D g) :
    ∃ y : D.I g, (y : G) ∈ rightResidual d ∧
      d.quotientMatrixEquiv (QuotientGroup.mk' _ y) = rightCubic := by
  let π := moduleProjection d.quotientSymmetricEquiv
  let a := Hypothesis.pairPermEquiv rightCubic
  have ha3 : a^3 = 1 := by
    change (Hypothesis.pairPermEquiv rightCubic)^3 = 1
    rw [← map_pow]
    have hc : rightCubic^3 = 1 := Prod.ext (one_pow 3) MatrixOrbit.cubic_cube
    rw [hc,map_one]
  have even_of_cube (x : Equiv.Perm (Fin 3)) (hx : x^3=1) :
      x ∈ alternatingGroup (Fin 3) := by
    change Equiv.Perm.sign x = 1
    have he := congrArg Equiv.Perm.sign hx
    rw [map_pow, map_one, Int.units_pow_eq_pow_mod_two] at he
    simpa using he
  have ha : a ∈ (D.L.subgroupOf (D.I g)).map π ⊓ ProductDecomposition.rightFactor := by
    constructor
    · rw [show (D.L.subgroupOf (D.I g)).map π =
        (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) from
        d.quotientSymmetricEquiv_L_image]
      exact ⟨even_of_cube a.1 (congrArg Prod.fst ha3),
        even_of_cube a.2 (congrArg Prod.snd ha3)⟩
    · constructor
      · change (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three) 1 = 1
        exact map_one _
      · trivial
  obtain ⟨y,hy,hey⟩ := mem_oddFactor_image_of_cube π D.L
    (d.I_eq_LU.symm ▸ le_sup_left) ProductDecomposition.rightFactor a ha ha3
  exact ⟨y,hy,Hypothesis.pairPermEquiv.injective hey⟩

private theorem matrix_perp_span (X : MatrixOrbit.M) (hX : X ≠ 0) (hs : X.det = 0)
    (v : MatrixOrbit.M)
    (hv : determinantForm.polarBilin v X = 0) :
    ∃ a : Fin 3 → ZMod 2, v = a 0 • X +
      a 1 • matrixAction MatrixOrbit.leftCubic X + a 2 • matrixAction rightCubic X := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    determinantForm_apply,determinantForm_apply,determinantForm_apply] at hv
  exact (show ∀ X : MatrixOrbit.M, X ≠ 0 → X.det = 0 → ∀ v : MatrixOrbit.M,
    (v + X).det - v.det - X.det = 0 → ∃ a : Fin 3 → ZMod 2,
      v = a 0 • X + a 1 • matrixAction MatrixOrbit.leftCubic X +
        a 2 • matrixAction rightCubic X by decide +kernel) X hX hs v hv

private theorem matrixLift_smul_mem (d : Hypothesis D g) (A : Subgroup G)
    (v : MatrixOrbit.M) (hv : matrixLift d (Multiplicative.ofAdd v) ∈ A)
    (a : ZMod 2) : matrixLift d (Multiplicative.ofAdd (a • v)) ∈ A := by
  fin_cases a
  · change matrixLift d (Multiplicative.ofAdd ((0 : ZMod 2) • v)) ∈ A
    simpa only [zero_smul, ofAdd_zero, map_one] using A.one_mem
  · change matrixLift d (Multiplicative.ofAdd ((1 : ZMod 2) • v)) ∈ A
    simpa only [one_smul] using hv

/-- The two original residual orbit planes span the marked perpendicular. -/
theorem exchanged_orbit_planes_span (d : Hypothesis D g) (t : G) (ht : t ∈ D.T)
    (he : conjugate (leftResidual d) t = rightResidual d) :
    localSpan D.V₁ (leftResidual d) ⊔
      conjugate (localSpan D.V₁ (leftResidual d)) t = D.V := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  have hleft := (span_le_liftedPlane d z hz).trans (liftedPlane_le_perpendicular d z)
  have htV : conjugate D.V t = D.V :=
    mem_normalizer_iff_map_conj_eq.mp (d.base.T_normalizes_V (D.T.inv_mem ht))
  apply le_antisymm (sup_le hleft ((map_mono hleft).trans_eq htV))
  change D.V ≤ localSpan D.V₁ (leftResidual d) ⊔
    conjugate (localSpan D.V₁ (leftResidual d)) t
  rw [orbit_plane_exchange d t ht he]
  let A := localSpan D.V₁ (leftResidual d) ⊔ localSpan D.V₁ (rightResidual d)
  have hpoint : matrixLift d (Multiplicative.ofAdd (d.pointVector z)) ∈ A := by
    have heq : matrixLift d (Multiplicative.ofAdd (d.pointVector z)) = (z : G) := by
      change (d.coordinates.symm (d.coordinates (inclusion (point_le_VL D) z)) : G) = z
      rw [d.coordinates.symm_apply_apply]
      rfl
    rw [heq]
    exact mem_sup_left (le_conjugateSpanBy _ _ z.property)
  have hlift (Y : Subgroup G) (i : D.I g) (hi : (i : G) ∈ Y) :
      matrixLift d (Multiplicative.ofAdd
        (matrixAction (d.quotientMatrixEquiv (QuotientGroup.mk' _ i)) (d.pointVector z))) ∈
        localSpan D.V₁ Y := by
    have heq := matrixLift_equivariant d i (Multiplicative.ofAdd (d.pointVector z))
    change matrixLift d (Multiplicative.ofAdd
      (matrixAction (d.quotientMatrixEquiv (QuotientGroup.mk' _ i)) (d.pointVector z))) = _ at heq
    rw [heq]
    have hp : matrixLift d (Multiplicative.ofAdd (d.pointVector z)) ∈ localSpan D.V₁ Y := by
      change (d.coordinates.symm (d.coordinates (inclusion (point_le_VL D) z)) : G) ∈ _
      rw [d.coordinates.symm_apply_apply]
      exact le_conjugateSpanBy _ _ z.property
    exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.V₁ Y hi) _).mp hp
  obtain ⟨l,hl,hlc,_⟩ := exists_left_cubic d
  obtain ⟨r,hr,hrc⟩ := exists_right_cubic d
  have hleftv : matrixLift d (Multiplicative.ofAdd
      (matrixAction MatrixOrbit.leftCubic (d.pointVector z))) ∈ A := by
    exact mem_sup_left (hlc ▸ hlift (leftResidual d) l hl)
  have hrightv : matrixLift d (Multiplicative.ofAdd
      (matrixAction rightCubic (d.pointVector z))) ∈ A := by
    exact mem_sup_right (hrc ▸ hlift (rightResidual d) r hr)
  intro x hx
  let v : D.VL := ⟨x,d.V_le_VL hx⟩
  obtain ⟨a,ha⟩ := matrix_perp_span (d.pointVector z) hz (d.pointVector_det z)
    (d.coordinates v).toAdd ((d.perpendicular v).mp hx z)
  have hxv : matrixLift d (d.coordinates v) = x := by
    change (d.coordinates.symm (d.coordinates v) : G) = x
    rw [d.coordinates.symm_apply_apply]
  rw [← hxv]
  change matrixLift d (Multiplicative.ofAdd (d.coordinates v).toAdd) ∈ A
  rw [ha]
  change matrixLift d ((Multiplicative.ofAdd (a 0 • d.pointVector z) *
    Multiplicative.ofAdd (a 1 • matrixAction MatrixOrbit.leftCubic (d.pointVector z))) *
    Multiplicative.ofAdd (a 2 • matrixAction rightCubic (d.pointVector z))) ∈ A
  rw [map_mul,map_mul]
  exact A.mul_mem (A.mul_mem (matrixLift_smul_mem d A _ hpoint _)
    (matrixLift_smul_mem d A _ hleftv _)) (matrixLift_smul_mem d A _ hrightv _)

/-- The same source interchange lies outside U C_T(V). The actual local
rank-one construction supplies the plane normalizer and order-four facts. -/
theorem exists_exchanging_partner (d : Hypothesis D g) (hex : FactorExchange d)
    (hU : D.U ≤ normalizer (localSpan D.V₁ (leftResidual d) : Set G))
    (hcard : Nat.card (localSpan D.V₁ (leftResidual d)) = 4) :
    ∃ t ∈ D.T, conjugate (leftResidual d) t = rightResidual d ∧
      t ∉ D.U ⊔ (D.T ⊓ centralizer (D.VL : Set G)) ∧
      localSpan D.V₁ (leftResidual d) ⊔
        conjugate (localSpan D.V₁ (leftResidual d)) t = D.V := by
  obtain ⟨t,ht,he⟩ := hex
  have he' := residual_exchange_of_factor_exchange d t ht he
  have hjoin := exchanged_orbit_planes_span d t ht he'
  refine ⟨t,ht,he',?_,hjoin⟩
  intro hin
  have hpV : localSpan D.V₁ (leftResidual d) ≤ D.VL :=
    conjugateSpanBy_mono le_rfl (leftResidual_le_L d)
  have hn : D.U ⊔ (D.T ⊓ centralizer (D.VL : Set G)) ≤
      normalizer (localSpan D.V₁ (leftResidual d) : Set G) :=
    sup_le hU (inf_le_right.trans ((centralizer_le hpV).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hfix : conjugate (localSpan D.V₁ (leftResidual d)) t =
      localSpan D.V₁ (leftResidual d) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem (hn hin))
  rw [hfix,sup_idem] at hjoin
  have hbad := d.V_card
  rw [← hjoin,hcard] at hbad
  norm_num at hbad

/-- The literal Chapter 15 natural action supplies the exchange, and the
chosen cubic supplies the order-four orbit plane. Only its actual local
normalization by U remains as the independent rank-one input. -/
theorem literal_exchanging_partner
    {M Z Zperp V Y T : Subgroup G} {g : G}
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hU : (Chapter15.setup Z Zperp Y T).U ≤
      normalizer (localSpan Z (leftResidual d) : Set G)) :
    ∃ t ∈ T, conjugate (leftResidual d) t = rightResidual d ∧
      t ∉ (Chapter15.setup Z Zperp Y T).U ⊔
        (T ⊓ centralizer (V : Set G)) ∧
      localSpan Z (leftResidual d) ⊔ conjugate (localSpan Z (leftResidual d)) t = Zperp := by
  obtain ⟨y,hy,hyc,_⟩ := exists_left_cubic d
  have hcard := (selected_plane d y hy hyc).2.2.1
  have hex := Multiplicity.Chapter15Exchange.literal_factorExchange a hTM hSyl hspan d
  have h := exists_exchanging_partner d hex hU hcard
  change ∃ t ∈ T, conjugate (leftResidual d) t = rightResidual d ∧
    t ∉ (Chapter15.setup Z Zperp Y T).U ⊔ (T ⊓ centralizer (localSpan Z Y : Set G)) ∧
    localSpan Z (leftResidual d) ⊔ conjugate (localSpan Z (leftResidual d)) t = Zperp at h
  simpa only [hspan] using h

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
