module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.SmallSections

/-!
# The paired source choice with its actual conjugating element

The source set in MS93 (5.7) is {d,d^x}. If the critical endpoint seed
normalizes both joined backward seeds, its inverse conjugate normalizes
the first one as well. The three source generators then normalize the
first joined seed. Its small local quotient places it in B, contradicting
the transported moving index. This proves the first alternative selection
in (5.7) with the exact generator from (5.6), rather than replacing that
generator by either of its two factors.

The radius-displacement consumer constructs a critical path from one of
the two choices, preserving the appropriate conjugated common edge and
the actual path overlap. Source (5.2)(iii) also supplies the triple
commutator for this same pair if both choices lie in the distant kernel.
The further nonnormalizing action comparison of (3.3) remains separate.

Source: Meierfrankenfeld--Stellmacher (1993), pp.917--919.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  (geometry : Geometry R)

omit [Finite M] in
private theorem paired_join_map_back {a d : Vertex R}
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a) :
    (Z R (act R x d) ⊔ Z R a).map (MulAut.conj x).toMonoidHom = Z R d ⊔ Z R a := by
  have hfix : act R x⁻¹ a = a := (stabilizer R a).inv_mem hx
  rw [Subgroup.map_sup]
  have h₁ := Z_act R x⁻¹ (act R x d)
  have h₂ := Z_act R x⁻¹ a
  rw [←act_mul,mul_inv_cancel,act_one] at h₁
  simpa only [inv_inv,hfix] using congrArg₂ (· ⊔ ·) h₁.symm h₂.symm

omit [Finite M] in
/-- Both endpoint normalizations imply normalization by the third, inverse
conjugated source generator. -/
theorem paired_endpoint_normalizes_first_join {a d e : Vertex R}
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a)
    (hn : Z R e ≤ normalizer
      ((Z R (act R x d) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) :
    Z R (act R x⁻¹ e) ≤ normalizer
      ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  have hm := map_mono (f := (MulAut.conj x).toMonoidHom) hn
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj x).bijective,
    paired_join_map_back x hx] at hm
  simpa only [Z_act,inv_inv] using hm

/-- First paragraph of (5.7): at least one chosen join is not normalized by
the endpoint seed. The local small-section assertion is already proved. -/
theorem exists_nonnormalized_paired_seed
    (hb : 2 < geometry.b R) {a d t e : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : stabilizer R a →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a)) (hS : 17 ∣ Nat.card S)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a)
    (hindex : (Z R t).relIndex (Z R d) ≤ 64)
    (hgen : stabilizer R a ≤ (Q R t ⊔ Z R e) ⊔ Z R (act R x⁻¹ e))
    (hmove : 1 < (B R a (geometry.Z_normal a)).relIndex (U R d)) :
    ∃ b ∈ ({d,act R x d} : Set (Vertex R)),
      ¬ Z R e ≤ normalizer ((Z R b ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  classical
  by_contra! h
  have h₁ := h d (by simp)
  have h₂ := paired_endpoint_normalizes_first_join x hx (h (act R x d) (by simp))
  have hn : stabilizer R a ≤ normalizer
      ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) :=
    hgen.trans (sup_le (sup_le (edge_normalizes_neighbor_seed_join hat hdt) h₁) h₂)
  have hc := small_normal_radius_commutator geometry hb ha q hq hk hp hS
    (Z R d ⊔ Z R a) (neighbor_seed_join_le_radius hat hdt) hn
    ((neighbor_seed_join_index_le geometry (by omega) ha hat hdt).trans hindex)
  have hU : U R d ≤ B R a (geometry.Z_normal a) :=
    (U_le_Z d).trans (le_sup_left.trans
      (radius_le_B_of_commutator geometry hb ha _ (neighbor_seed_join_le_radius hat hdt) hc))
  have hi := relIndex_eq_one.mpr hU
  omega

omit [Finite M] in
/-- The pair selected in (5.5)/(5.6) remains in the same radius, including
the second edge transported by the source conjugator. -/
theorem paired_seed_le_radius {a d t : Vertex R}
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a) :
    Z R d ⊔ Z R (act R x d) ≤ V R a := by
  have hfix : act R x a = a := hx
  have hatx : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdtx := (adjacent_act_iff R x _ _).mpr hdt
  exact sup_le (le_sup_left.trans (neighbor_seed_join_le_radius hat hdt))
    (le_sup_left.trans (neighbor_seed_join_le_radius hatx hdtx))

omit [Finite M] in
/-- The actual pair satisfies the source triple commutator under its common
backward-kernel containment; this uses (5.2)(ii), hence (5.2)(iii). -/
theorem paired_kernel_triple_commutator {a d t e c : Vertex R}
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a)
    (hc : ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)))
    (h₁ : Z R d ≤ Q R c) (h₂ : Z R (act R x d) ≤ Q R c) :
    ⁅⁅X R e ⊓ Q R a,Z R d ⊔ Z R (act R x d)⁆,
      Z R d ⊔ Z R (act R x d)⁆ = ⊥ := by
  have hp := le_inf (paired_seed_le_radius hat hdt x hx) (sup_le h₁ h₂)
  have ht := SectionFive.critical_radius_triple_commutator (R := R) hc (a' := e) (c := c)
  exact le_bot_iff.mp ((commutator_mono (commutator_mono le_rfl hp) hp).trans_eq ht)

/-- The paired source generation yields a backward critical path from the
local radius-displacement estimate, with the actual chosen edge and overlap. -/
theorem paired_backward_path_of_radius_displacement
    (hb : 2 < geometry.b R) {a d t e : Vertex R}
    (p : CriticalPath R geometry a e) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : stabilizer R a →* S) (hq : Function.Surjective q)
    (hk : q.ker = (Q R a).subgroupOf (stabilizer R a))
    (hp : IsPGroup 2 (Q R a)) (hS : 17 ∣ Nat.card S)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a)
    (hindex : (Z R t).relIndex (Z R d) ≤ 64)
    (hgen : stabilizer R a ≤ (Q R t ⊔ Z R e) ⊔ Z R (act R x⁻¹ e))
    (hmove : 1 < (B R a (geometry.Z_normal a)).relIndex (U R d))
    (hdisp : ⁅V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R e⁆ ≤ Z R a) :
    ∃ b ∈ ({d,act R x d} : Set (Vertex R)), ∃ v,
      Adjacent R a v ∧ Adjacent R b v ∧
      ∃ r : CriticalPath R geometry b (p.walk.getVert (p.walk.length-2)),
        r.walk.getVert 1 = v ∧
        ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨b,hbmem,hn⟩ := exists_nonnormalized_paired_seed geometry hb p.start_color
    hat hdt q hq hk hp hS x hx hindex hgen hmove
  have hV : Z R b ≤ V R a := by
    rcases hbmem with rfl | rfl
    · exact le_sup_left.trans (paired_seed_le_radius hat hdt x hx)
    · exact le_sup_right.trans (paired_seed_le_radius hat hdt x hx)
  have hnot : ¬ Z R b ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply hn
    apply le_normalizer_iff.mpr
    intro z hz y hy
    have hzZ := (p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R a)
    have hd : ⁅Z R e,Z R b⁆ ≤ Z R a := by
      rw [commutator_comm]
      exact (commutator_mono (le_inf hV hbad) le_rfl).trans hdisp
    have hm : (Z R b ⊔ Z R a).map (MulAut.conj z).toMonoidHom ≤ Z R b ⊔ Z R a := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨v,hv,rfl⟩
        have hc := hd (commutator_mem_commutator hz hv)
        change z*v*z⁻¹ ∈ Z R b ⊔ Z R a
        rw [show z*v*z⁻¹ = ⁅z,v⁆*v by simp [commutatorElement_def,mul_assoc]]
        exact mul_mem (mem_sup_right hc) (mem_sup_left hv)
      · rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hzZ hz)]
        exact le_sup_right
    exact hm (mem_map_of_mem (MulAut.conj z).toMonoidHom hy)
  refine ⟨b,hbmem,?_⟩
  rcases hbmem with rfl | rfl
  · exact ⟨t,hat,hdt,exists_backward_path_of_not_le geometry (by omega) p hat hdt hnot⟩
  · have hfix : act R x a = a := hx
    have hatx : Adjacent R a (act R x t) := by
      rw [←hfix]
      exact (adjacent_act_iff R x _ _).mpr hat
    have hdtx := (adjacent_act_iff R x _ _).mpr hdt
    exact ⟨act R x t,hatx,hdtx,
      exists_backward_path_of_not_le geometry (by omega) p hatx hdtx hnot⟩

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
