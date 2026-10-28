module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.PairedChoice
public import Theory.GroupAction.TwoPerfectSmallSection
public import Theory.GroupTheory.PResidual.FiniteLocalPair

/-!
# The small fixed kernel in the original backward shift

The source generators need normalize only the kernel join under the local
residual. The actual simple quotient restricts onto that residual, so its
small two-section is fixed. This puts the original centralizer kernel in B,
and its index bounds the moving index of the prescribed backward U-layer.
The final consumer constructs the native backward critical path and keeps
every overlap equality from the original path.

The source 3.3 kernel index and source 5.5/5.6 normalization clauses remain
explicit earlier inputs; this module does not claim the full 5.7 or 5.8.
Source: Meierfrankenfeld–Stellmacher (1993), (5.7), printed p.919.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  (geometry : Geometry R)

/-- The same whole-stabilizer quotient restricts onto the local residual. -/
theorem exists_residual_simple_projection
    {a : Vertex R} {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : stabilizer R a →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S) :
    ∃ r : Ltilde R a →* S, Function.Surjective r ∧ IsPGroup 2 r.ker ∧
      ∀ l, r l = q (inclusion (Ltilde_le_stabilizer a) l) := by
  let := finite_stabilizer R a
  have hperfect : IsPPerfect 2 S := by
    intro N hN hp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N hN with hn | hn
    · subst N
      have htwo : IsPGroup 2 S := hp.of_equiv (QuotientGroup.quotientBot)
      obtain ⟨n,hn⟩ := htwo.exists_card_eq
      have hd : 17 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 17) (hn ▸ hS)
      norm_num at hd
    · exact hn
  let r := q.comp (inclusion (Ltilde_le_stabilizer a))
  refine ⟨r,?_,hk.comap_of_injective _ (inclusion_injective _),fun _ => rfl⟩
  intro y
  have hm : (pResidual 2 (stabilizer R a)).map q = ⊤ :=
    (map_pResidual_of_surjective 2 q hq).trans ((pResidual_eq_top_iff 2 S).mpr hperfect)
  obtain ⟨z,hz,hzy⟩ := (show y ∈ (pResidual 2 (stabilizer R a)).map q by rw [hm]; trivial)
  refine ⟨⟨z,mem_map_of_mem (stabilizer R a).subtype hz⟩,?_⟩
  exact hzy

/-- The residual, rather than the whole stabilizer, suffices to fix the section. -/
theorem small_residual_radius_commutator
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (hp : IsPGroup 2 (Q R a))
    (H : Subgroup (FreeAmalgam R)) (hH : H ≤ V R a)
    (hn : Ltilde R a ≤ normalizer (H : Set _))
    (hi : (Z R a).relIndex H ≤ 64) : ⁅H,Ltilde R a⁆ ≤ Z R a := by
  let := finite_stabilizer R a
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  have hHQ := hH.trans (geometry.V_le_Q hb a ha)
  have hHG : H ≤ stabilizer R a := hHQ.trans (fun _ hx => hx.1)
  let : Finite H := Finite.of_injective (inclusion hHG) (inclusion_injective _)
  exact commutator_le_of_twoPerfect_simple_seventeen_small_section
    (Ltilde R a) H (Z R a) (isPPerfect_embedded_pResidual_of_finite 2 _) q hq hk hS
    (hp.to_le hHQ) hn ((Ltilde_le_stabilizer a).trans (Z_normalized R a))
    (normal_subgroupOf_of_le_normalizer (hHG.trans (Z_normalized R a))) hi

/-- The actual preimage B contains the small residual-invariant radius subgroup. -/
theorem small_residual_radius_le_B
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (hp : IsPGroup 2 (Q R a))
    (H : Subgroup (FreeAmalgam R)) (hH : H ≤ V R a)
    (hn : Ltilde R a ≤ normalizer (H : Set _))
    (hi : (Z R a).relIndex H ≤ 64) : H ≤ B R a (geometry.Z_normal a) :=
  radius_le_B_of_commutator geometry hb ha H hH
    (small_residual_radius_commutator geometry hb ha q hq hk hS hp H hH hn hi)

/-- The two actual source generators fix the kernel of the distant action modulo Z. -/
theorem neighbor_kernel_le_B_of_source_generators
    (hb : 2 < geometry.b R) {a d t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (hp : IsPGroup 2 (Q R a))
    (A J E : Subgroup (FreeAmalgam R))
    (hindex : (Z R t).relIndex (Z R d) ≤ 64)
    (hgen : Ltilde R a ≤ J ⊔ E)
    (hJ : J ≤ normalizer (((Z R d ⊓ centralizer (A : Set _)) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _))
    (hE : E ≤ normalizer (((Z R d ⊓ centralizer (A : Set _)) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) :
    Z R d ⊓ centralizer (A : Set _) ≤ B R a (geometry.Z_normal a) := by
  let H := (Z R d ⊓ centralizer (A : Set _)) ⊔ Z R a
  have hH : H ≤ Z R d ⊔ Z R a := sup_le_sup inf_le_left le_rfl
  have hHV := hH.trans (neighbor_seed_join_le_radius hat hdt)
  let := finite_Z R d
  let := finite_Z R a
  let := finite_stabilizer R a
  have hsup : Z R d ⊔ Z R a ≤ stabilizer R a :=
    (neighbor_seed_join_le_radius hat hdt).trans
      ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1))
  let : Finite (Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hsup) (inclusion_injective _)
  have hi : (Z R a).relIndex H ≤ 64 :=
    (relIndex_le_of_le_right hH index_ne_zero_of_finite).trans
      ((neighbor_seed_join_index_le geometry (by omega) ha hat hdt).trans hindex)
  exact le_sup_left.trans (small_residual_radius_le_B geometry hb ha q hq hk hS hp H hHV
    (hgen.trans (sup_le hJ hE)) hi)


/-- A literal kernel in B bounds the moving index of the whole backward U-layer. -/
theorem movingIndex_le_of_centralizer_kernel
    {a d : Vertex R} (A : Subgroup (FreeAmalgam R))
    (hker : Z R d ⊓ centralizer (A : Set _) ≤ B R a (geometry.Z_normal a))
    {n : ℕ} (hindex : (centralizer (A : Set _)).relIndex (Z R d) ≤ n) :
    (B R a (geometry.Z_normal a)).relIndex (U R d) ≤ n := by
  let := finite_Z R d
  have hi : (B R a (geometry.Z_normal a)).relIndex (Z R d) ≤ n := by
    apply le_trans (relIndex_le_of_le_left hker index_ne_zero_of_finite)
    simpa only [inf_relIndex_left] using hindex
  exact (relIndex_le_of_le_right (U_le_Z d) index_ne_zero_of_finite).trans hi

/-- The source residual generators and the small/root centralizer index
contradict the strict moving-index hypothesis of (5.7). -/
theorem no_large_mover_of_kernel_generators
    (hb : 2 < geometry.b R) {a d t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (hp : IsPGroup 2 (Q R a))
    (A J E : Subgroup (FreeAmalgam R))
    (hindex : (Z R t).relIndex (Z R d) ≤ 64)
    (hgen : Ltilde R a ≤ J ⊔ E)
    (hJ : J ≤ normalizer (((Z R d ⊓ centralizer (A : Set _)) ⊔ Z R a :
      Subgroup (FreeAmalgam R)) : Set _))
    (hE : E ≤ normalizer (((Z R d ⊓ centralizer (A : Set _)) ⊔ Z R a :
      Subgroup (FreeAmalgam R)) : Set _))
    (hsmall : (centralizer (A : Set _)).relIndex (Z R d) ≤ 4) :
    ¬ 4 < (B R a (geometry.Z_normal a)).relIndex (U R d) := by
  exact not_lt_of_ge (movingIndex_le_of_centralizer_kernel geometry A
    (neighbor_kernel_le_B_of_source_generators geometry hb ha hat hdt
      q hq hk hS hp A J E hindex hgen hJ hE) hsmall)

/-- The source fixed-kernel comparison yields the actual backward critical
path, using the original distant X-layer and first-neighborhood kernel. -/
theorem source57_backward_path_of_kernel_comparison
    (hb : 2 < geometry.b R) {a d t e : Vertex R}
    (path : CriticalPath R geometry a e)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : stabilizer R a →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hS : 17 ∣ Nat.card S) (hp : IsPGroup 2 (Q R a))
    (J : Subgroup (FreeAmalgam R))
    (hindex : (Z R t).relIndex (Z R d) ≤ 64)
    (hgen : Ltilde R a ≤ J ⊔ Z R e)
    (hJ : Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      J ≤ normalizer (((Z R d ⊓ centralizer ((X R e ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _))
        ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _))
    (hE : Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      Z R e ≤ normalizer (((Z R d ⊓ centralizer ((X R e ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _))
        ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _))
    (hsmall : Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      (centralizer ((X R e ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)).relIndex (Z R d) ≤ 4)
    (hmove : 4 < (B R a (geometry.Z_normal a)).relIndex (U R d)) :
    (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
      back.walk.getVert 1 = t ∧
      ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
      ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  have hqker : IsPGroup 2 q.ker := by rw [hk]; exact hp.comap_subtype
  obtain ⟨r,hr,hrker,_⟩ := exists_residual_simple_projection q hq hqker hS
  have hn : ¬ Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro hc
    exact no_large_mover_of_kernel_generators geometry hb path.start_color hat hdt
      r hr hrker hS hp (X R e ⊓ Q R a) J (Z R e) hindex hgen
      (hJ hc) (hE hc) (hsmall hc) hmove
  exact ⟨exists_backward_path_of_not_le geometry (by omega) path hat hdt hn,
    fun h => hn ((le_sup_left.trans (neighbor_seed_join_le_radius hat hdt)).trans h)⟩

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
