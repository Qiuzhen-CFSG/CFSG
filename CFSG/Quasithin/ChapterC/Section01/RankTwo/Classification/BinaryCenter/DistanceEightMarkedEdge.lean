module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceFourMarkedEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.OriginalEarlier

/-!
# The distance-eight edge image in its natural marking

The preceding source indices give an elementary four-group whose fixed
space on U is a plane. Thus this same marked image is a common-axis offender
on two natural copies. DistanceEightMovement uses it to move the literal
characteristic replacement while fixing the original Sylow-fixed natural line.

Source: MS93 (4.4), printed p.890; Aschbacher--Smith C.1.34(4), pp.136--137.
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

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


omit [Finite M] in
/-- The index-two central edge layer forces every edge square into the M-kernel. -/
private theorem edge_square_centralizes (common : CommonFacts R source geometry) (earlier : CoreFactors.Earlier R geometry)
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
    (earlier.edge_Z_index _ _ rfl hab)
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
private theorem edge_image_square (common : CommonFacts R source geometry) (earlier : CoreFactors.Earlier R geometry)
    (r : M) (hr : r ∈ R) : source.projection r ^ 2 = 1 := by
  have hr' : embedM R r ∈ Q R (beta R) := by
    rw [Q_beta]
    exact mem_map_of_mem _ hr
  have hh := edge_square_centralizes common earlier (embedM R r) hr'
  rw [← map_pow] at hh
  have hc : r ^ 2 ∈ pCore 2 M := by
    rw [← Q_alpha_comap R source.two_group source.core_le]
    exact hh
  rw [← map_pow]
  exact show r ^ 2 ∈ source.projection.ker from source.projection_kernel.symm ▸ hc

/-- The source (4.4) edge index gives order four in the original marked quotient. -/
private theorem edge_image_card (source : LocalSource L R) (earlier : CoreFactors.Earlier R geometry) : Nat.card (R.map source.projection) = 4 := by
  have hab : Adjacent R (alpha R) (beta R) :=
    (adjacent_iff_exists_common R _ _).mpr ⟨1, Or.inl ⟨rfl, rfl⟩⟩
  have hi := earlier.edge_Q_index _ _ rfl hab
  rw [Q_alpha R source.two_group source.core_le, Q_beta,
    relIndex_map_map_of_injective _ _ (embedM_injective R)] at hi
  rw [← relIndex_ker, source.projection_kernel]
  exact hi

private theorem natural_fixed_iff (common : CommonFacts R source geometry)
    (u : U R (alpha R)) :
    (common.natural.equiv u).toAdd ∈ fixedSpace BinaryLinearThree.W
        (R.map (common.natural.marking.toMonoidHom.comp source.projection)) ↔
      (u : FreeAmalgam R) ∈ centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
  constructor
  · intro hu r hr
    rw [Q_beta] at hr
    obtain ⟨r,hr,rfl⟩ := hr
    let v : U R (alpha R) := (U R (alpha R)).normalizerMonoidHom
      ⟨embedM R r,common.natural.normalized ⟨r,rfl⟩⟩ u
    have hv := common.natural.action r u v rfl
    have hf := hu ⟨common.natural.marking (source.projection r),r,hr,rfl⟩
    have he : v = u := common.natural.equiv.injective
      (Multiplicative.toAdd.injective (hv.trans hf))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  · intro hu a
    obtain ⟨r,hr,he⟩ := a.property
    have hh := common.natural.action r u u (by
      rw [hu (embedM R r) (by rw [Q_beta]; exact mem_map_of_mem _ hr),mul_inv_cancel_right])
    change BinaryLinearThree.W (a : SL) (common.natural.equiv u).toAdd = _
    rw [← he]
    exact hh.symm

/-- The source edge index is the fixed-plane count for the same marked matrix image. -/
theorem marked_edge_fixed_card (common : CommonFacts R source geometry)
    (earlier : CoreFactors.Earlier R geometry) :
    Nat.card (fixedSpace BinaryLinearThree.W
      (R.map (common.natural.marking.toMonoidHom.comp source.projection))) = 4 := by
  let C := (centralizer (Q R (beta R) : Set (FreeAmalgam R))).subgroupOf (U R (alpha R))
  let f : C ≃ fixedSpace BinaryLinearThree.W
      (R.map (common.natural.marking.toMonoidHom.comp source.projection)) := {
    toFun u := ⟨(common.natural.equiv u).toAdd,(natural_fixed_iff common u).mpr u.property⟩
    invFun v := ⟨common.natural.equiv.symm (Multiplicative.ofAdd (v : BinaryLinearThree.Vector)),
      (natural_fixed_iff common _).mp (by
        rw [MulEquiv.apply_symm_apply]
        exact v.property)⟩
    left_inv u := Subtype.ext (common.natural.equiv.symm_apply_apply u)
    right_inv v := Subtype.ext (congrArg Multiplicative.toAdd
      (common.natural.equiv.apply_symm_apply (Multiplicative.ofAdd (v : BinaryLinearThree.Vector)))) }
  have hC : C = (Z R (beta R)).subgroupOf (U R (alpha R)) := by
    ext u
    change (u : FreeAmalgam R) ∈ centralizer (Q R (beta R) : Set (FreeAmalgam R)) ↔
      (u : FreeAmalgam R) ∈ Z R (beta R)
    rw [DistanceFour.Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)]
    exact (and_iff_right ((MS93.U_le_Z _) u.property)).symm
  have hi : C.index = 2 := by
    rw [hC]
    change (Z R (beta R)).relIndex (U R (alpha R)) = 2
    rw [← DistanceFour.Early.edge_Z_index_eq_natural common (alpha R) (beta R) rfl (base_adjacent R)]
    exact earlier.edge_Z_index _ _ rfl (base_adjacent R)
  have hc := C.card_mul_index
  rw [hi, common.natural.card_at _ rfl] at hc
  rw [← Nat.card_congr f]
  omega

/-- In the natural marking the genuine distance-eight replacement image is a
common-axis offender on two copies of the natural module. -/
theorem marked_edge_offender (common : CommonFacts R source geometry)
    (earlier : CoreFactors.Earlier R geometry) :
    IsOffender (BinaryLinearThree.W.prod BinaryLinearThree.W)
      (R.map (common.natural.marking.toMonoidHom.comp source.projection)) := by
  let E := R.map (common.natural.marking.toMonoidHom.comp source.projection)
  have hc : Nat.card E = 4 := by
    change Nat.card (R.map (common.natural.marking.toMonoidHom.comp source.projection)) = 4
    rw [← map_map, card_map_of_injective common.natural.marking.injective]
    exact edge_image_card source earlier
  have he : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hc
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      obtain ⟨r,hr,hrx⟩ := x.property
      change (x : SL) ^ 2 = 1
      rw [← hrx]
      change common.natural.marking (source.projection r) ^ 2 = 1
      rw [← map_pow, edge_image_square common earlier r hr, map_one]) }
  have hf : Module.finrank (ZMod 2) (fixedSpace BinaryLinearThree.W E) = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace BinaryLinearThree.W E)
    rw [Nat.card_zmod, marked_edge_fixed_card common earlier] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hh.symm
  change IsOffender (BinaryLinearThree.W.prod BinaryLinearThree.W) E
  refine ⟨⟨?_,he⟩,?_⟩
  · intro hh
    rw [hh] at hc
    have hone : Nat.card (⊥ : Subgroup SL) = 1 := Nat.card_unique
    omega
  · rw [fixedCodim_prod]
    have hh := fixedCodim_add_finrank BinaryLinearThree.W E
    have hd : Module.finrank (ZMod 2) BinaryLinearThree.Vector = 3 := by simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    rw [hf,hd] at hh
    have hr : rank E = 2 := by rw [rank,hc]; decide
    omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight
