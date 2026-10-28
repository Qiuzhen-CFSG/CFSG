module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootTrappedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelectedPaths

/-!
# Full-seed commutators for the equal-mover critical-root selector

The root-case decomposition of X retains every central attachment. Its
ambient-fixed summand lies in an adjacent edge omega, so X equals Z.
The maximizing plane makes a small-index mover quadratic on this whole
X-layer. Equal neighboring movers then put their entire central omega in
the original seed and their full neighbor commutator in that central omega.

Apply these containments at the same two conjugates selected in MS93 (5.6).
The original B-relative moving index supplies nonnormality and is preserved
at both neighbors. The whole-Z fixed equality identifies the intersection
of their central omegas with the full ambient-fixed subgroup of Z. In
particular the two distant-X commutators have ambient-fixed intersection.
The individual commutators still need comparison to exclude the remaining
trapped alternative in (5.7); the path alternative retains every overlap.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii) and (5.6)--(5.7),
printed pp.867,917--919, refs/Pushing up weak BN-pairs of rank two.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem fixed_X_le_seed {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t) :
    X R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) ≤ Z R a := by
  have ht : color R t=true := by
    have hh := adjacent_color_ne R hat
    rw [ha] at hh
    cases ht : color R t <;> simp_all
  apply le_trans _ (adjacent_Z_le R ha hat)
  intro x hx
  rw [Z,if_neg (by rw [ht]; decide)]
  obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hx.1
  exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h R ht hat hxQ,hx2,
    fun y hy => hx.2 y (hy.2 a (adjacent_symm R hat))⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full central omega equals the source seed in the critical-root case. -/
theorem Input.replacement_root_X_eq_Z
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    X d.radical a = Z d.radical a := by
  apply le_antisymm
  · rw [h.replacement_root_X_decomposition_center d path hb hsmall]
    exact sup_le (U_le_Z a) (fixed_X_le_seed d.radical path.start_color hat)
  · exact geometry.omega_bound a path.start_color (by
      rw [geometry.distance_constant a path.start_color]
      exact lt_of_lt_of_le (by decide : 0 < 4) hb)

omit h in
private theorem commutator_split_bound {G : Type*} [Group G]
    (X U D J : Subgroup G) [IsMulCommutative X]
    (hUX : U ≤ X) (hX : X=U ⊔ D) (hDJ : D ≤ centralizer (J : Set G))
    (hJn : J ≤ normalizer (U : Set G)) : ⁅X,J⁆ ≤ ⁅U,J⁆ := by
  have hcommU : ⁅U,J⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hJn
  have hn : X ≤ normalizer ((⁅U,J⁆ : Subgroup G) : Set G) :=
    (X.le_centralizer.trans (centralizer_le (hcommU.trans hUX))).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [hX]
  apply commutator_sup_le_of_relative_normal X U D J ⁅U,J⁆ hn hUX
    (le_sup_right.trans_eq hX.symm) le_rfl
  rw [commutator_eq_bot_iff_le_centralizer.mpr hDJ]
  exact bot_le

/-- A small-index mover acts quadratically on the entire X-layer in the
root case, including its ambient-fixed summand. -/
theorem Input.replacement_root_small_index_X_quadratic
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hi : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ⁅⁅X d.radical a,J⁆,J⁆=⊥ := by
  dsimp only
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let S := stabilizer d.radical a
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb path.start_color hat
  have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb path.start_color hat B hB f hfQ hTf hindex hmax hi
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hUX : U d.radical a ≤ X d.radical a := (U_le_Z a).trans
    (geometry.omega_bound a path.start_color (by
      rw [geometry.distance_constant a path.start_color]
      exact lt_of_lt_of_le (by decide : 0 < 4) hb))
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer _ a)
  have hq := le_bot_iff.mp ((commutator_mono (commutator_mono le_rfl hJP) hJP).trans_eq hquad)
  have hq' := congrArg (Subgroup.map S.subtype) hq
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hUS,
    map_subgroupOf_eq_of_le hJS,Subgroup.map_bot] at hq'
  let := X_elementary d.radical a
  have hbound := commutator_split_bound (X d.radical a) (U d.radical a)
    (X d.radical a ⊓ centralizer (S : Set (FreeAmalgam d.radical))) J hUX
    (h.replacement_root_X_decomposition_center d path hb hsmall)
    (inf_le_right.trans (centralizer_le hJS)) (hJS.trans (U_normalized a))
  exact le_bot_iff.mp ((commutator_mono hbound le_rfl).trans_eq hq')


omit [CharP F 2] in
private theorem core_le_mover
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh

/-- Equal neighboring movers in the critical-root plane branch have their
whole central omega in the starting seed. Their action on the whole neighbor
seed has commutator inside that same central omega. -/
theorem Input.replacement_equal_root_neighbor_commutator
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hi : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    omegaCenter J ≤ Z d.radical a ∧
      ⁅Z d.radical c,J⁆ ≤ omegaCenter J := by
  dsimp only
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hXa := h.replacement_root_X_eq_Z d path hb hat hsmall
  have hquad := h.replacement_root_small_index_X_quadratic d path hb hat hsmall hi
  have hQJ := core_le_mover h d path.start_color hat
  have hJS : J ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have homega : omegaCenter J ≤ Z d.radical a := by
    rw [←hXa]
    intro x hx
    obtain ⟨hxJ,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
    have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
    have hxQ : x ∈ Q d.radical a := hC ▸
      (show x ∈ C d.radical a from ⟨hJS hxJ,fun y hy =>
        hxc y (hQJ (omegaCenter_le _ (hXa.ge hy)))⟩)
    exact mem_omegaCenter_iff.mpr ⟨hxQ,hx2,fun y hy => hxc y (hQJ hy)⟩
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm _ hat) (adjacent_symm _ hct)
  have hgt : act d.radical g t=t := hg
  have hJg : J.map (MulAut.conj g⁻¹).toMonoidHom=J := by
    have hh := Subgroup.SmallMover.join_map (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    rw [←U_act,←Q_act,←Q_act,hga,hgt] at hh
    exact hh.trans hequal
  have hXcg : X d.radical c = (X d.radical a).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [←hga,X_act]
  have hquadC : ⁅⁅X d.radical c,J⁆,J⁆=⊥ := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hquad
    rwa [map_commutator,map_commutator,hJg,←hXcg,Subgroup.map_bot] at hh
  have hQcJ : Q d.radical c ≤ J := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hQJ
    rwa [hJg,←Q_act,hga] at hh
  have hXc : X d.radical c=Z d.radical c := by
    rw [←hga,X_act,Z_act,hXa]
  have hJSc : J ≤ stabilizer d.radical c := by
    change Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) ≤ _
    rw [←hequal]
    exact (Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hx => hx.2 c (adjacent_symm _ hct))
  have hcommX : ⁅Z d.radical c,J⁆ ≤ X d.radical c := by
    rw [←hXc]
    exact le_normalizer_iff_commutator_le_left.mp (hJSc.trans (X_normalized _ c))
  have hcommJ : ⁅Z d.radical c,J⁆ ≤ J :=
    hcommX.trans ((omegaCenter_le _).trans hQcJ)
  have hcommC : ⁅Z d.radical c,J⁆ ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    rw [←hXc]
    exact commutator_eq_bot_iff_le_centralizer.mp hquadC
  refine ⟨homega,fun x hx => ?_⟩
  exact mem_omegaCenter_iff.mpr ⟨hcommJ hx,(mem_omegaCenter_iff.mp (hcommX hx)).2.1,hcommC hx⟩


omit h in
private theorem conjugate_seed_commutator {G : Type*} [Group G]
    (Y J Q Z : Subgroup G) (hcenter : omegaCenter J ≤ Z)
    (hcomm : ⁅Y,Q⁆ ≤ omegaCenter J)
    (k : G) (hkQ : k ∈ normalizer (Q : Set G))
    (hkZ : k ∈ normalizer (Z : Set G)) :
    omegaCenter (J.map (MulAut.conj k).toMonoidHom) ≤ Z ∧
      ⁅Y.map (MulAut.conj k).toMonoidHom,Q⁆ ≤
        omegaCenter (J.map (MulAut.conj k).toMonoidHom) := by
  have hZ := mem_normalizer_iff_map_conj_eq.mp hkZ
  have hQ := mem_normalizer_iff_map_conj_eq.mp hkQ
  change Z.map (MulAut.conj k).toMonoidHom = Z at hZ
  change Q.map (MulAut.conj k).toMonoidHom = Q at hQ
  constructor
  · have hh := map_mono (f := (MulAut.conj k).toMonoidHom) hcenter
    rwa [←omegaCenter_map _ _ (MulAut.conj k).injective,hZ] at hh
  · have hh := map_mono (f := (MulAut.conj k).toMonoidHom) hcomm
    rwa [map_commutator,←omegaCenter_map _ _ (MulAut.conj k).injective,hQ] at hh

omit h in
private theorem mover_act {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) (g : FreeAmalgam R) (a t : Vertex R) (q : ℕ) :
    Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
      (Q R (act R g t)) q =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) q).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]

omit h in
private theorem omega_pair_of_full_fixed {G : Type*} [Group G]
    (Z Q J₁ J₂ S : Subgroup G) (hZ : Z ≤ omegaCenter Q)
    (hQ₁ : Q ≤ J₁) (hQ₂ : Q ≤ J₂) (hJ₁ : J₁ ≤ S) (hJ₂ : J₂ ≤ S)
    (hcenter₁ : omegaCenter J₁ ≤ Z)
    (hfixed : (Z ⊓ centralizer (J₁ : Set G)) ⊓ centralizer (J₂ : Set G) =
      Z ⊓ centralizer (S : Set G)) :
    omegaCenter J₁ ⊓ omegaCenter J₂ = Z ⊓ centralizer (S : Set G) := by
  apply le_antisymm
  · rintro w ⟨hw₁,hw₂⟩
    rw [←hfixed]
    exact ⟨⟨hcenter₁ hw₁,(mem_omegaCenter_iff.mp hw₁).2.2⟩,
      (mem_omegaCenter_iff.mp hw₂).2.2⟩
  · rintro w ⟨hwZ,hwS⟩
    obtain ⟨hwQ,hw2,_⟩ := mem_omegaCenter_iff.mp (hZ hwZ)
    exact ⟨mem_omegaCenter_iff.mpr ⟨hQ₁ hwQ,hw2,centralizer_le hJ₁ hwS⟩,
      mem_omegaCenter_iff.mpr ⟨hQ₂ hwQ,hw2,centralizer_le hJ₂ hwS⟩⟩

/-- The source equal-mover root selector retains both original B-relative
moving indices. Both full neighbor commutators with Q lie in the central
omega of their own smaller mover, and hence in the original Z-layer.
Generation, full-Z fixed equality, critical-root movement, the maximizing
parabolic and every path overlap all use these same two conjugates. -/
theorem Input.replacement_equal_root_moving_selected_commutators
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a
      (geometry.Z_normal a)).relIndex (U d.radical c))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
        (U d.radical c₁) =
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
          (U d.radical c) ∧
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
        (U d.radical c₂) =
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
          (U d.radical c) ∧
      omegaCenter J₁ ≤ Z d.radical a ∧ omegaCenter J₂ ≤ Z d.radical a ∧
      ⁅Z d.radical c₁,Q d.radical a⁆ ≤ omegaCenter J₁ ∧
      ⁅Z d.radical c₂,Q d.radical a⁆ ≤ omegaCenter J₂ ∧
      omegaCenter J₁ ⊓ omegaCenter J₂ =
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical c₁,X d.radical z ⊓ Q d.radical a⁆ ⊓
        ⁅Z d.radical c₂,X d.radical z ⊓ Q d.radical a⁆ ≤
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₁ : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₂ : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
        (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
          Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
            (Z d.radical z ⊓ Q d.radical a) ∧
          X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
          ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) := by
  have hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_index_le
      geometry (by omega) path.start_color hat hct).trans
      (h.replacement_root_neighbor_seed_index_le_cube d path hb hat hct hsmall)
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hBY := h.replacement_small_radius_le_B d geometry (by omega) path.start_color
      (Z d.radical c ⊔ Z d.radical a)
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hct)
      ((Ltilde_le_stabilizer a).trans hn)
      (lt_of_le_of_lt hidx ((pow_lt_pow_iff_right₀ hq).mpr (by decide)))
    have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hBY)
    rw [hone] at hmove
    exact (not_lt_of_ge hq.le) hmove
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
    hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,hchoice⟩ :=
      h.replacement_equal_small_index_selected_root_alternative d path hb hat hfirst hct
        hnormal hequal hsmall hJm
  let J := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have hxinv := (stabilizer d.radical a).inv_mem hxS
  obtain ⟨homega,hcomm⟩ := h.replacement_equal_root_neighbor_commutator d path hb hat hct
    hsmall hJm hequal
  have hbase : ⁅Z d.radical c,Q d.radical a⁆ ≤ omegaCenter J := by
    rw [show J = Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) from hequal]
    exact (commutator_mono le_rfl (core_le_mover h d path.start_color hat)).trans hcomm
  have homega' : omegaCenter J ≤ Z d.radical a := by simpa only [J,hequal] using homega
  obtain ⟨hcenter₁,hcomm₁⟩ := conjugate_seed_commutator (Z d.radical c) J
    (Q d.radical a) (Z d.radical a) homega' hbase g
    (Q_normalized d.radical a hgS) (Z_normalized d.radical a hgS)
  obtain ⟨hcenter₂,hcomm₂⟩ := conjugate_seed_commutator
    ((Z d.radical c).map (MulAut.conj g).toMonoidHom)
    (J.map (MulAut.conj g).toMonoidHom) (Q d.radical a) (Z d.radical a)
    hcenter₁ hcomm₁ x⁻¹ (Q_normalized d.radical a hxinv) (Z_normalized d.radical a hxinv)
  have hi₁ := CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.movingIndex_act
    geometry (d := c) (by omega) path.start_color g⁻¹
      ((stabilizer d.radical a).inv_mem hgS)
  have hi₂ := CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.movingIndex_act
    geometry (d := act d.radical g⁻¹ c) (by omega) path.start_color x hxS
  have hQJ : Q d.radical a ≤ J := by
    simpa only [J,hequal] using core_le_mover h d path.start_color hat
  have hQJ₁ : Q d.radical a ≤ J.map (MulAut.conj g).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hQJ
    simpa only [MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hgS)] using hh
  have hQJ₂ : Q d.radical a ≤ (J.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hQJ₁
    simpa only [MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hxinv)] using hh
  have hJ₁S : J.map (MulAut.conj g).toMonoidHom ≤ stabilizer d.radical a := by
    have hh := (show _ ≤ _ from le_sup_left.trans le_sup_left).trans_eq hgen₁
    simpa only [mover_act,inv_inv] using hh
  have hJ₂S : (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤
      stabilizer d.radical a := by
    have hh := (show _ ≤ _ from le_sup_left.trans le_sup_left).trans_eq hgen₂
    simpa only [mover_act,inv_inv] using hh
  have hcenters := omega_pair_of_full_fixed (Z d.radical a) (Q d.radical a)
    (J.map (MulAut.conj g).toMonoidHom)
    ((J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom)
    (stabilizer d.radical a)
    (show Z d.radical a ≤ omegaCenter (Q d.radical a) from
      (h.replacement_root_X_eq_Z d path hb hat hsmall).ge)
    hQJ₁ hQJ₂ hJ₁S hJ₂S hcenter₁ (by
      simpa only [mover_act,inv_inv] using hfixed)
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
    hi₁,hi₂.trans hi₁,?_,?_,?_,?_,?_,?_,hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,hchoice⟩
  · simpa only [mover_act,inv_inv] using hcenter₁
  · simpa only [mover_act,inv_inv] using hcenter₂
  · simpa only [mover_act,Z_act,inv_inv] using hcomm₁
  · simpa only [mover_act,Z_act,inv_inv] using hcomm₂
  · simpa only [mover_act,inv_inv] using hcenters
  · have hA : X d.radical z ⊓ Q d.radical a ≤ Q d.radical a := inf_le_right
    have hh := (inf_le_inf
      ((commutator_mono (le_refl ((Z d.radical c).map (MulAut.conj g).toMonoidHom)) hA).trans hcomm₁)
      ((commutator_mono (le_refl (((Z d.radical c).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj x⁻¹).toMonoidHom)) hA).trans hcomm₂)).trans_eq hcenters
    simpa only [mover_act,Z_act,inv_inv] using hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
