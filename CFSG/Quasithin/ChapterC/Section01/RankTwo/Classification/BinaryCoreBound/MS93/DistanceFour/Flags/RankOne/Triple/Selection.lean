module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore


/-!
# Selection of the marked parabolic at critical distance four

The source index-two inclusion Z_beta ≤ Z_alpha makes every element of
Q_beta act on Z_alpha with square one: it fixes Z_beta pointwise and its
displacement lies in that subgroup. The faithful edge action then places
squares in Q_alpha. The image of R in the original SL₃(2) quotient therefore
has order four and exponent two.

In the binary upper triangular group, a square-one matrix has either its
(0,1) or its (1,2) entry zero. These are the two actual parabolic cores.
The subgroup union lemma selects one core, and lifting through the two-group
kernel identifies the original R with the intrinsic parabolic two-core.
The flag and quotient marking are retained throughout.

Source: Meierfrankenfeld--Stellmacher (1993), the first (4.6.6) on p.903
and the parabolic selection preceding (4.6.8), printed p.905. The subsequent
triple-commutator argument is not a conclusion of this module.
-/

public section

open Subgroup Matrix
open Matrix.PSL3Two
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

private theorem square_one_borel (g : SL) (hg : g ∈ borelSL) (hs : g ^ 2 = 1) :
    g ∈ pointParabolicSL.pCoreIn 2 ∨ g ∈ lineParabolicSL.pCoreIn 2 := by
  obtain ⟨h10, h20, h21⟩ := (mem_borelSL_iff g).mp hg
  have hd := g.property
  rw [det_fin_three] at hd
  simp only [h10, h20, h21, mul_zero, zero_mul, sub_zero, add_zero] at hd
  have hdiag : ∀ a b c : ZMod 2, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1 := by
    decide
  obtain ⟨h00, h11, h22⟩ := hdiag _ _ _ hd
  have h02 := congrArg (fun x : SL => x.val 0 2) hs
  rw [pow_two] at h02
  change (g.val * g.val) 0 2 = 0 at h02
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h00, h22, one_mul, mul_one] at h02
  have hab : g.val 0 1 * g.val 1 2 = 0 := by
    have htwo : g.val 0 2 + g.val 0 2 = 0 := by
      have h : ∀ x : ZMod 2, x + x = 0 := by decide
      exact h _
    linear_combination h02 - htwo
  rcases mul_eq_zero.mp hab with h01 | h12
  · right
    rw [lineParabolicSL_pCoreIn_two_eq_R]
    refine ⟨Multiplicative.ofAdd (g.val 0 2, g.val 1 2), ?_⟩
    apply Subtype.ext
    change !![1,0,g.val 0 2; 0,1,g.val 1 2; 0,0,1] = g.val
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h10, h20, h21, h01]
  · left
    rw [MarkedProduct.pointParabolic_core]
    exact ⟨h00, h10, h20, h11, h12, h21, h22⟩


private theorem model_core_card (g : SL) (i : Bool) :
    Nat.card ((modelParabolic g i).pCoreIn 2) = 4 := by
  rw [pCoreIn, Nat.card_congr ((pCore 2 (modelParabolic g i)).equivMapOfInjective
    (modelParabolic g i).subtype (modelParabolic g i).subtype_injective).toEquiv.symm]
  exact (ParabolicCoreModel.core_data (modelParabolicEquivSymmetric g i)).2

private theorem model_core_selection (g : SL) (A : Subgroup SL)
    (hA : A ≤ modelBorel g) (hcard : Nat.card A = 4)
    (hsquare : ∀ a ∈ A, a ^ 2 = 1) :
    ∃ i : Bool, A = (modelParabolic g i).pCoreIn 2 := by
  let f := (MulAut.conj g).toMonoidHom
  let K := A.comap f
  have hKB : K ≤ borelSL := by
    intro x hx
    have hh := hA hx
    rw [modelBorel_eq_map] at hh
    simpa only [f, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      (mem_map_equiv).mp hh
  have hK : K ≤ pointParabolicSL.pCoreIn 2 ∨ K ≤ lineParabolicSL.pCoreIn 2 := by
    apply SubgroupClass.subset_union.mp
    intro x hx
    apply square_one_borel x (hKB hx)
    apply (MulAut.conj g).injective
    rw [map_pow, map_one]
    exact hsquare _ hx
  have hm : K.map f = A := map_comap_eq_self_of_surjective (MulAut.conj g).surjective A
  have hex : ∃ i : Bool, A ≤ (modelParabolic g i).pCoreIn 2 := by
    rcases hK with h | h
    · refine ⟨false, ?_⟩
      rw [← hm]
      exact (map_mono h).trans_eq (map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective)
    · refine ⟨true, ?_⟩
      rw [← hm]
      exact (map_mono h).trans_eq (map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective)
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, eq_of_le_of_card_ge hi (by rw [model_core_card, hcard])⟩

private theorem fixed_index_two_square {G : Type*} [Group G] (H : Subgroup G)
    (hi : H.index = 2) (hpow : ∀ x : G, x ^ 2 = 1)
    (e : MulAut G) (hfixed : ∀ x ∈ H, e x = x) : e ^ 2 = 1 := by
  have hmem (x : G) : e x ∈ H ↔ x ∈ H := by
    constructor
    · intro hx
      exact e.injective (hfixed (e x) hx) ▸ hx
    · intro hx
      exact (hfixed x hx).symm ▸ hx
  apply MulEquiv.ext
  intro x
  let d := x⁻¹ * e x
  have hd : d ∈ H := by
    rw [H.mul_mem_iff_of_index_two hi]
    simp only [H.inv_mem_iff, hmem]
  have hstep : e x = x * d := by simp [d]
  change e (e x) = x
  rw [hstep, map_mul, hfixed d hd, hstep, mul_assoc, ← pow_two, hpow, mul_one]


open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
/-- The index-two central edge layer forces every edge square into the M-kernel. -/
theorem edge_square_centralizes (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (r : FreeAmalgam R) (hr : r ∈ Q R (beta R)) : r ^ 2 ∈ Q R (alpha R) := by
  have hab : Adjacent R (alpha R) (beta R) :=
    (adjacent_iff_exists_common R _ _).mpr ⟨1, Or.inl ⟨rfl, rfl⟩⟩
  have hloc : Q R (beta R) ≤ stabilizer R (alpha R) :=
    fun _ hx => hx.2 _ (adjacent_symm R hab)
  have hn := Z_normalized R (alpha R) (hloc hr)
  let e : MulAut (Z R (alpha R)) := (Z R (alpha R)).normalizerMonoidHom ⟨r, hn⟩
  have hZb : Z R (beta R) = omegaCenter (Q R (beta R)) := by
    rw [Z, if_neg (by change true ≠ false; decide : color R (beta R) ≠ false)]
    rfl
  have he : e ^ 2 = 1 := fixed_index_two_square
    ((Z R (beta R)).subgroupOf (Z R (alpha R)))
    (early.edge_Z_index _ _ rfl hab)
    (fun z => Subtype.ext (by
      have hz : (z : FreeAmalgam R) ∈ omegaCenter (Q R (alpha R)) := by
        exact (common.X_eq_Z _ rfl).ge z.property
      exact (mem_omegaCenter_iff.mp hz).2.1)) e (by
      intro z hz
      apply Subtype.ext
      change r * (z : FreeAmalgam R) * r⁻¹ = z
      have hz' : (z : FreeAmalgam R) ∈ Z R (beta R) := hz
      rw [hZb] at hz'
      have hc := (mem_omegaCenter_iff.mp hz').2.2 r hr
      rw [hc, mul_inv_cancel_right])
  rw [← common.centralizer _ _ rfl hab]
  refine ⟨(Q R (beta R)).pow_mem hr 2, ?_⟩
  intro z hz
  have hh := congrArg (fun a : MulAut (Z R (alpha R)) => (a ⟨z, hz⟩ : FreeAmalgam R)) he
  change r * (r * z * r⁻¹) * r⁻¹ = z at hh
  have hh' : r ^ 2 * z * (r ^ 2)⁻¹ = z := by
    calc
      _ = r * (r * z * r⁻¹) * r⁻¹ := by simp only [pow_two, _root_.mul_inv_rev]; group
      _ = z := hh
  exact (mul_inv_eq_iff_eq_mul.mp hh').symm

/-- The edge image in the original marked quotient has exponent two. -/
theorem edge_image_square (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (r : M) (hr : r ∈ R) : source.projection r ^ 2 = 1 := by
  have hr' : embedM R r ∈ Q R (beta R) := by
    rw [Q_beta]
    exact mem_map_of_mem _ hr
  have hh := edge_square_centralizes source geometry common early (embedM R r) hr'
  rw [← map_pow] at hh
  have hc : r ^ 2 ∈ pCore 2 M := by
    rw [← Q_alpha_comap R source.two_group source.core_le]
    exact hh
  rw [← map_pow]
  exact show r ^ 2 ∈ source.projection.ker from source.projection_kernel.symm ▸ hc

/-- The first (4.6.6) gives order four in the original marked quotient. -/
theorem edge_image_card (source : LocalSource L R) (geometry : Geometry R)
    (early : EarlyFacts R geometry) : Nat.card (R.map source.projection) = 4 := by
  have hab : Adjacent R (alpha R) (beta R) :=
    (adjacent_iff_exists_common R _ _).mpr ⟨1, Or.inl ⟨rfl, rfl⟩⟩
  have hi := early.edge_Q_index _ _ rfl hab
  rw [Q_alpha R source.two_group source.core_le, Q_beta,
    relIndex_map_map_of_injective _ _ (embedM_injective R)] at hi
  rw [← relIndex_ker, source.projection_kernel]
  exact hi

/-- The marked parabolic selection immediately preceding source (4.6.8). -/
theorem select_flag_kernel (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry) :
    ∃ i : Bool, flagKernel source i = Q R (beta R) := by
  obtain ⟨i, hi⟩ := model_core_selection source.flag (R.map source.projection)
    (map_le_iff_le_comap.mpr source.edge_in_borel) (edge_image_card source geometry early)
    (by rintro _ ⟨r, hr, rfl⟩; exact edge_image_square source geometry common early r hr)
  let P := parabolic source.projection source.flag i
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  have hkerP : source.projection.ker ≤ P := by
    intro x hx
    change source.projection x ∈ modelParabolic source.flag i
    rw [show source.projection x = 1 from hx]
    exact one_mem _
  have hcore : source.projection.ker ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hk hkerP le_normalizer_of_normal
  have hm := map_pCoreIn_of_ker_isPGroup source.projection hk P
  have hpmap : P.map source.projection = modelParabolic source.flag i :=
    map_comap_eq_self_of_surjective source.projection_surjective _
  rw [hpmap, ← hi] at hm
  have he := congrArg (Subgroup.comap source.projection) hm
  rw [comap_map_eq_self hcore,
    comap_map_eq_self (source.projection_kernel.symm ▸ source.core_le)] at he
  refine ⟨i, ?_⟩
  change (P.pCoreIn 2).map (embedM R) = Q R (beta R)
  rw [he, Q_beta]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
