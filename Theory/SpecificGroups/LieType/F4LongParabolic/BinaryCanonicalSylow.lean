module
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCanonicalParabolic
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryQuotient
/-!
# The full Sylow subgroup on the original binary F4 parabolic

The canonical positive subgroup maps to a noncommutative two-subgroup of
SL3(2): its two long simple root elements do not commute. The image therefore
has order eight. Pulling it back through the actual quotient, whose kernel
is the two-core already contained in the positive subgroup, proves that the
positive subgroup is a full Sylow subgroup of the original matrix parabolic.

This identifies the literal Sylow subgroup needed to transport MS3 in
`MS93.OriginalAction.F4Input`. The comparison does not replace the original
overgroup or its commutator core.

Sources: Aschbacher--Smith C.1.31 (MS3), printed p.135; the F4 example of
Meierfrankenfeld--Stellmacher (1993), printed p.831. Matrix certificates use
the integral Geck tables from `A02ParabolicSections.SourceLevi.F4`.
-/

public noncomputable section
open Subgroup Thompson.BinaryMatrix
namespace Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates.Canonical
private def leviAB : Array ℕ := #[570425345, 8589934594, 4, 8, 16, 32, 64, 2688, 320, 2560, 1280, 2048, 4096, 2236416, 16384, 8945664, 69632, 2228224, 278528, 8912896, 1114112, 2097152, 4456448, 8388608, 16777216, 570425344, 9227468802, 2281701376, 285212672, 536870912, 26910654465, 36507222016, 4580179968, 9126805504, 25769803777, 34359738368, 68719476736, 137438953472, 412316860416, 549755813888, 1511828488192, 2748779069440, 6597069766656, 8796093022208, 17592186044416, 35184372088832, 105553116266496, 140737488355328, 387028092977152, 703687441776640, 1688849860263936, 2251799813685248]
private def leviBA : Array ℕ := #[33554433, 9126805506, 4, 8, 16, 32, 64, 640, 320, 2560, 1344, 2048, 4096, 139264, 16384, 557056, 69632, 2228224, 278528, 8912896, 1118208, 2097152, 4472832, 8388608, 16777216, 570425344, 100663298, 36641439744, 285212672, 536870912, 18354274306, 36507222016, 4563402752, 9126805504, 26340229121, 34359738368, 68719476736, 137438953472, 412316860416, 549755813888, 1374389534720, 2748779069440, 7146825580544, 8796093022208, 17592186044416, 35184372088832, 105553116266496, 140737488355328, 351843720888320, 703687441776640, 1829587348619264, 2251799813685248]
private lemma leviAB_product : decode 52 rows21 * decode 52 rows23 = decode 52 leviAB := by
  apply decode_mul
  decide +kernel
private lemma leviBA_product : decode 52 rows23 * decode 52 rows21 = decode 52 leviBA := by
  apply decode_mul
  decide +kernel
private lemma positive_levis_not_commute : levi 0 * levi 2 ≠ levi 2 * levi 0 := by
  intro hh
  have hm := congrArg (fun x : Matˣ => x.val) hh
  change decode 52 rows21 * decode 52 rows23 = decode 52 rows23 * decode 52 rows21 at hm
  rw [leviAB_product,leviBA_product] at hm
  have he := congrFun (congrFun hm 0) 29
  exact (show decode 52 leviAB 0 29 ≠ decode 52 leviBA 0 29 from by decide +kernel) he
open QuotientModel

private def leviProjection : A →* Matrix.PSL3Two.SL :=
  projection.comp (inclusion (show A ≤ P from le_sup_right))

private theorem leviProjection_injective : Function.Injective leviProjection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  have hk : leviProjection.ker = E.subgroupOf A := by
    rw [leviProjection, ← MonoidHom.comap_ker, projection_ker]
    rfl
  have hp : IsPGroup 2 leviProjection.ker := hk.symm ▸
    E_isPGroup.comap_of_injective A.subtype A.subtype_injective
  have simple_of_equiv {B : Type} [Group B] (e : B ≃* Matrix.PSL3Two.SL) :
      IsSimpleGroup B := by
    let : IsSimpleGroup Matrix.PSL3Two.PSL :=
      Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
    exact e.isSimpleGroup
  let : IsSimpleGroup A := simple_of_equiv leviEquiv
  rcases (inferInstance : leviProjection.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let : Group.IsPerfect A := A_isPerfect
    have hA : IsPGroup 2 A := (h ▸ hp).of_equiv topEquiv
    exact (Group.IsPerfect.not_isNilpotent A hA.isNilpotent).elim

private def sylowImage : Subgroup Matrix.PSL3Two.SL := (U.subgroupOf P).map projection

private lemma sylowImage_noncommutative : ¬ IsMulCommutative sylowImage := by
  intro hc
  let := hc
  let a : A := ⟨levi 0,levi_mem 0⟩
  let b : A := ⟨levi 2,levi_mem 2⟩
  have ha : leviProjection a ∈ sylowImage :=
    mem_map_of_mem projection (positive_levi_mem_U 0)
  have hb : leviProjection b ∈ sylowImage :=
    mem_map_of_mem projection (positive_levi_mem_U 1)
  have he : a*b = b*a := leviProjection_injective (by
    rw [map_mul,map_mul]
    exact setLike_mul_comm ha hb)
  have hm := congrArg (fun x : A => (x : Matˣ)) he
  change levi 0 * levi 2 = levi 2 * levi 0 at hm
  exact positive_levis_not_commute hm

private theorem sylowImage_card : Nat.card sylowImage = 8 := by
  have hp : IsPGroup 2 sylowImage := U_isPGroup.comap_subtype.map projection
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd : 2^n ∣ 168 := by
    rw [← hn, ← Matrix.PSL3Two.card_SL]
    exact sylowImage.card_subgroup_dvd_card
  have hb : n ≤ 3 := by
    by_contra hh
    have hh := (pow_dvd_pow 2 (by omega : 4 ≤ n)).trans hd
    norm_num at hh
  interval_cases n
  · have hi : IsCyclic sylowImage := isCyclic_of_card_dvd_prime (p := 2) (by rw [hn]; norm_num)
    exact (sylowImage_noncommutative hi.isMulCommutative).elim
  · have hi : IsCyclic sylowImage := isCyclic_of_card_dvd_prime (p := 2) (by rw [hn]; norm_num)
    exact (sylowImage_noncommutative hi.isMulCommutative).elim
  · exact (sylowImage_noncommutative (IsPGroup.isMulCommutative_of_card_eq_prime_sq hn)).elim
  · exact hn

/-- The canonical positive subgroup is a full Sylow subgroup of the original parabolic. -/
noncomputable def originalSylow : Sylow 2 P :=
  let T : Sylow 2 Matrix.PSL3Two.SL := Sylow.ofCard sylowImage (by
    rw [Matrix.PSL3Two.card_SL]
    rw [show 2 ^ (Nat.factorization 168) 2 = 8 from by decide +kernel]
    exact sylowImage_card)
  T.comapOfKerIsPGroup projection
    (projection_ker.symm ▸ E_isPGroup.comap_subtype)
    (by rw [MonoidHom.range_eq_top.mpr projection_surjective]; exact le_top)

theorem originalSylow_coe : (originalSylow : Subgroup P) = U.subgroupOf P := by
  change (sylowImage).comap projection = U.subgroupOf P
  rw [sylowImage, comap_map_eq, projection_ker]
  exact sup_eq_left.mpr (comap_mono E_le_U)

end Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates.Canonical
