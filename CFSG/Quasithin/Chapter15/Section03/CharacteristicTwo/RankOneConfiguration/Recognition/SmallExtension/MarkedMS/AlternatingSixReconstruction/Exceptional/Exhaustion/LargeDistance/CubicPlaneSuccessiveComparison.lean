module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedCore
/-!
# Shifted comparison on two successive selected cubic paths

Keep critical paths a--v--c--t--z and d--s--a--v--c, with the
selected edge cores generating at a and c. Suppose the forward slice
at a and both endpoint slices at c are strict, and retain the actual
conjugator in G_a sending c to d. A failed shifted comparison gives the
nontrivial full-kernel line H. The earlier strict-forward argument makes
H central in G_a. The two strict slices at c put H in both its generating
edge seeds, hence in Z(G_c). Conjugating by the retained element of G_a
then makes H central in G_d, contradicting its proved noncentrality there.
This proves the comparison for both cover orders, including the entire
order-32 central attachment, without identifying it with a critical line.

The actual outer selector supplies the two strict midpoint slices and
midpoint generation for the next comparison. Its same component switch,
both generation equations, chosen backward path and every overlap vertex
are retained. The next path's escape, strict forward slice and generating
backward configuration remain explicit; constructing these simultaneously,
the other slice cases and the terminal source assembly are still required.

Whole-core and literal C.1.32 applications keep the original radical and
cubic projection, whose kernel is E with potentially nontrivial odd E/Q.
No Sylow hypothesis on that radical or extra normalization hypothesis is
used. This is the successive-selection branch of the shifted comparison,
not a proof of all of (5.12), either core exhaustion, or reconstruction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the first center argument in (5.12)(1), printed pp.924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- Two successive selected configurations give the shifted comparison on
both full covers. The midpoint generation and its two strict slices supply
the second centrality needed by the source's terminal center argument. -/
theorem plane_shifted_comparison_of_two_selected_slices
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)))
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgd : act Rg g (p.walk.getVert 2) = d)
    (hmidgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a))
    (hforward : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z)) :
    ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆ := by
  by_contra hfail
  let H := ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
  have hcA : H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :=
    plane_shifted_failure_central_of_strict_forward h e hz hk u hR hb4 hsmall
      p q hqa hescape K hK hfail hgen hs
  have hr := plane_shifted_kernel_failure_reciprocal h e hz hk u hR hb4 hsmall
    p q hqa hescape K hK hfail
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  have hline := plane_four_full_kernel_line h e hz hk u hR hb4 hsmall p
    (V Rg a ⊓ Q Rg (p.walk.getVert 2)) inf_le_left inf_le_right (by rwa [hXZ])
  rw [hXZ] at hline
  have hHc : H ≤ Z Rg (p.walk.getVert 2) := hline.2.2.1.trans inf_le_right
  have hHz : H ≤ Z Rg z := hr.2.2.2.2.1.trans (inf_le_right.trans (DistanceEight.U_le_Z Rg z))
  have hHa : H ≤ Z Rg a := hline.2.2.1.trans inf_le_left
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hHv : H ≤ Z Rg (p.walk.getVert 1) :=
    (le_inf hHa hHc).trans_eq
      (plane_strict_slice_eq_edge h e hz hk u hR q.end_color p.start_color hcv hav hback).2.1
  have hHt : H ≤ Z Rg (p.walk.getVert 3) :=
    (le_inf hHz hHc).trans_eq
      (plane_strict_slice_eq_edge h e hz hk u hR q.end_color p.end_color hct hzt hforward).2.1
  have hcC : H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) :=
    (le_inf hHv hHt).trans
      ((plane_generating_edge_seed_intersection h e hz hk u hR q.end_color hcv hct hmidgen).le.trans
        inf_le_right)
  have hm : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      ((le_centralizer_iff.mp hcA).trans (Subgroup.centralizer_le_normalizer _)
        ((stabilizer Rg a).inv_mem hg))
  have hcD := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcC).trans
    (map_centralizer_le_centralizer_image _ _)
  change H.map (MulAut.conj g⁻¹).toMonoidHom ≤
    centralizer (((stabilizer Rg (p.walk.getVert 2)).map
      (MulAut.conj g⁻¹).toMonoidHom) : Set (FreeAmalgam Rg)) at hcD
  rw [hm,←stabilizer_act,hgd] at hcD
  have he : H = ⊥ := by
    have hh := hr.2.2.2.2.2.2.1
    change H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) = ⊥ at hh
    rwa [inf_eq_left.mpr hcD] at hh
  have hc : Nat.card H = 2 := hline.1
  rw [he,Subgroup.card_bot] at hc
  omega

include h e hz hk in
/-- The outer selected path supplies the midpoint generation and both strict
slices for the next shifted comparison, with every overlap retained. -/
theorem plane_selected_successive_comparison
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g (p.walk.getVert 2)
          let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
            ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
              q.walk.getVert 1 = t ∧
              (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
              ∀ b (q' : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2)),
                q'.walk.getVert 2 = d →
                (¬ ⁅V Rg d ⊓ Q Rg (q.walk.getVert 2),Z Rg (v.walk.getVert 2)⁆ ≤ Z Rg d) →
                Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d →
                2 < (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (q.walk.getVert 2)) →
                ∀ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 2) = b →
                ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg b ⊓ Q Rg (q.walk.getVert 2) →
                  ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤
                    ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ ⊔ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
          comparison z p ∨ comparison (act Rg x z) p' := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hc1 : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,r,hr,p',hverts,hps,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,halt⟩ :=
    plane_small_critical_backward_shift h e hz hk u hR p (hsmall _ _ p) hc1 hs
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat'] at hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl ha1] at hnorm hinside
  have hfirst : Q Rg t ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg hat))
        (fun _ hv => hv.2 _ (adjacent_symm Rg ha1))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hs' : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p'.walk.getVert 2)) := by
    have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h) hb
        (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [hverts 2]
    change 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x (p.walk.getVert 2)))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hs
  refine ⟨t,hat,r,hr,p',hverts,hgen,hpair,g,hg,hgt,?_⟩
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have cast_end {d v w : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) d v)
      (he : v = w) : ∃ q' : CriticalPath Rg (sourceGeometry h) d w,
        ∀ i, q'.walk.getVert i = q.walk.getVert i := by
    subst w
    exact ⟨q,fun _ => rfl⟩
  have finish {w : Vertex Rg}
      (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2)) (v.walk.getVert 2))
      (hq1 : q.walk.getVert 1 = t)
      (hqv : ∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i)
      (hgenq : Q Rg t ⊔ Q Rg (v.walk.getVert 1) = stabilizer Rg (alpha Rg))
      (hsv : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (v.walk.getVert 2)))
      (b : Vertex Rg) (q' : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2))
      (hq'd : q'.walk.getVert 2 = act Rg g (p.walk.getVert 2))
      (he : ¬ ⁅V Rg (act Rg g (p.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2),
        Z Rg (v.walk.getVert 2)⁆ ≤ Z Rg (act Rg g (p.walk.getVert 2)))
      (hgg : Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 1) =
        stabilizer Rg (act Rg g (p.walk.getVert 2)))
      (hss : 2 < (B Rg (act Rg g (p.walk.getVert 2)) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (q.walk.getVert 2)))
      (k : FreeAmalgam Rg) (hkG : k ∈ stabilizer Rg (act Rg g (p.walk.getVert 2)))
      (hkb : act Rg k (q.walk.getVert 2) = b)
      (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg b ⊓ Q Rg (q.walk.getVert 2)) :
      ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤
        ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg (act Rg g (p.walk.getVert 2))⁆ ⊔
          ⁅Z Rg (act Rg g (p.walk.getVert 2)),Z Rg (v.walk.getVert 2)⁆ := by
    have hqa : q.walk.getVert 2 = alpha Rg := by
      simpa only [SimpleGraph.Walk.getVert_zero] using hqv 0 (by omega)
    apply plane_shifted_comparison_of_two_selected_slices h e hz hk u hR hb4 hsmall
      q q' hq'd he K hK hgg hss k hkG hkb
    · rw [hqa,hq1,hqv 1 (by omega)]
      exact hgenq
    · simpa only [hqa] using hstrict
    · simpa only [hqa] using hsv
  rcases halt with ⟨q,hq1,hqv⟩ | ⟨q,hq1,hqv⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p.walk.getVert (p.walk.length-2) =
        p.walk.getVert 2 by rw [hl])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    exact Or.inl ⟨q',hq1',hqv',finish p q' hq1' hqv' hfirst hs⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p'.walk.getVert (p'.walk.length-2) =
        p'.walk.getVert 2 by rw [hl'])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    exact Or.inr ⟨q',hq1',hqv',finish p' q' hq1' hqv' (by rwa [hQfirst]) hs'⟩

omit hk in
include h e hz in
/-- The original whole-core reduction supplies the outer selection and its
midpoint conditions for the next comparison, on both full moving covers. -/
theorem coreExhaustion_or_cubic_successive_comparison :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
        ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
          let x := (embedM Rg r)⁻¹
          ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
            (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
            (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
            Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
              let d := act Rg g (p.walk.getVert 2)
              let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
                ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
                  q.walk.getVert 1 = t ∧
                  (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
                  ∀ b (q' : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2)),
                    q'.walk.getVert 2 = d →
                    (¬ ⁅V Rg d ⊓ Q Rg (q.walk.getVert 2),Z Rg (v.walk.getVert 2)⁆ ≤ Z Rg d) →
                    Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d →
                    2 < (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (q.walk.getVert 2)) →
                    ∀ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 2) = b →
                    ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg b ⊓ Q Rg (q.walk.getVert 2) →
                      ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤
                        ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ ⊔ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
              comparison z p ∨ comparison (act Rg x z) p')) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall z p hstrict
    exact plane_selected_successive_comparison h e hz hk u hplane hb4 hsmall p hstrict

omit hk in
include h e hz in
/-- Literal C.1.32 application of the successive comparison, with the
original projection, radical, full attachments and both covers retained. -/
theorem rankTwo_or_cubic_successive_comparison :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
        ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
          let x := (embedM Rg r)⁻¹
          ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
            (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
            (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
            Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
              let d := act Rg g (p.walk.getVert 2)
              let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
                ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
                  q.walk.getVert 1 = t ∧
                  (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
                  ∀ b (q' : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2)),
                    q'.walk.getVert 2 = d →
                    (¬ ⁅V Rg d ⊓ Q Rg (q.walk.getVert 2),Z Rg (v.walk.getVert 2)⁆ ≤ Z Rg d) →
                    Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d →
                    2 < (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (q.walk.getVert 2)) →
                    ∀ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 2) = b →
                    ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg b ⊓ Q Rg (q.walk.getVert 2) →
                      ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤
                        ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ ⊔ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
              comparison z p ∨ comparison (act Rg x z) p')) :=
  (coreExhaustion_or_cubic_successive_comparison h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
