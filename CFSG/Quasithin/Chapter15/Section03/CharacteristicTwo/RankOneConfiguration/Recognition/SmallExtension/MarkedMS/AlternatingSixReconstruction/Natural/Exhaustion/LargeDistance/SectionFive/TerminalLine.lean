module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ShiftChain
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Inputs

/-!
# The full-point terminal contradiction with both central covers

A quadratic four-subgroup of the eight-element point core contains its
unique transposition. Its displacement on either the natural module or the
augmentation cover is fixed by the point core and noncentral in S₆. A small
certificate on the eight core elements proves the subgroup assertion. The
literal cover equivalence and replacement projection then give a noncentral
element in the critical commutator fixed by its first edge kernel. The
small-image branch already has this property for its entire critical line.

Thus the intersection of the critical commutator with its first edge seed
is noncentral at the critical start, including for the order-thirty-two
cover. Two successive generating edges would make this same intersection
central, first at the intermediate vertex and then at the preceding one.
The actual component transporter fixes the subgroup pointwise and carries
that centrality back to the critical start, giving a contradiction.

The checked backward shifts supply both generating edges above distance
four in the full point-core branch. This proves distance at most four on
the original minimum characteristic replacement, preserving both cover
orders, the canonical quotient, the component transporter and path vertices.
The final literal replacement application leaves only the source-(5.12)
distance-four exclusion explicit in this branch. Other radical images and
the unconditional `LargeDistanceInput` remain to be proved.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), (5.10)--(5.12),
printed pp.866--867, 921--927. The generating-edge argument adapts
`SymplecticSetup.LargeDistance.false_of_three_shift_generators` using a
noncentral fixed subline instead of a zero-center assumption on the cover.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace TerminalLine
private abbrev a : S := swap01 * swap23
private abbrev b : S := Equiv.swap 0 2 * Equiv.swap 1 3
private def eight : List S := [1,a,b,a*b,swap45,swap45*a,swap45*b,swap45*(a*b)]
private theorem eight_closed : ∀ x ∈ eight, ∀ y ∈ eight, x*y ∈ eight := by
  have h : eight.all (fun x => eight.all (fun y => decide (x*y ∈ eight))) = true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using h
private theorem eight_inverses : ∀ x ∈ eight, x⁻¹ ∈ eight := by
  have h : eight.all (fun x => decide (x⁻¹ ∈ eight)) = true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using h
private def certificate : Subgroup S where
  carrier := {x | x ∈ eight}
  one_mem' := by decide +kernel
  mul_mem' := fun hx hy => eight_closed _ hx _ hy
  inv_mem' := eight_inverses _
private theorem core_in_certificate : pointCore ≤ certificate := by
  rw [pointCore_eq_closure,closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl <;> change _ ∈ eight <;> decide +kernel

private def pairFull (i j : Fin 6) : Full (Fin 6) := Pi.single i 1 + Pi.single j 1
private def cross (g h : S) : Full (Fin 6) :=
  pairFull (g (h 0)) (g (h 4)) - pairFull (g 0) (g 4) -
    (pairFull (h 0) (h 4) - pairFull 0 4)
private theorem quadratic_coordinate (A : Subgroup S) (hq : QuadraticPointCore.Quadratic A)
    (g h : S) (hg : g ∈ A) (hh : h ∈ A) : cross g h 0 = cross g h 4 := by
  have he := hq g hg h hh (pairVector 0 4)
  rw [map_sub,pairVector_map,pairVector_map,pairVector_map] at he
  have hz := congrArg Subtype.val (sub_eq_zero.mpr he)
  change (constants (Fin 6)).mkQ (pairFull (g (h 0)) (g (h 4))) -
    (constants (Fin 6)).mkQ (pairFull (g 0) (g 4)) -
      ((constants (Fin 6)).mkQ (pairFull (h 0) (h 4)) -
        (constants (Fin 6)).mkQ (pairFull 0 4)) = 0 at hz
  rw [←map_sub,←map_sub,←map_sub] at hz
  have hc : cross g h ∈ constants (Fin 6) := (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
  have h0 := congrFun hc (0:Fin 6)
  have h4 := congrFun hc (4:Fin 6)
  simpa only [Pi.smul_apply,allOne,smul_eq_mul,mul_one] using h0.symm.trans h4

private theorem quadratic_pair_certificate : ∀ g ∈ eight, ∀ k ∈ eight,
    g ≠ 1 → k ≠ 1 → g ≠ k → cross g k 0 = cross g k 4 →
    g = swap45 ∨ k = swap45 ∨ g*k = swap45 := by
  have h : eight.all (fun g => eight.all (fun k => decide
    (g ≠ 1 → k ≠ 1 → g ≠ k → cross g k 0 = cross g k 4 →
      g = swap45 ∨ k = swap45 ∨ g*k = swap45))) = true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using h

private theorem quadratic_four_contains_swap (A : Subgroup S) (hA : A ≤ pointCore)
    (hq : QuadraticPointCore.Quadratic A) (hc : 4 ≤ Nat.card A) : swap45 ∈ A := by
  by_contra hn
  have hne : A ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  obtain ⟨g,hg,hg1⟩ := (A.bot_or_exists_ne_one).resolve_left hne
  have hle : A ≤ zpowers g := by
    intro k hk
    by_cases hk1 : k = 1
    · rw [hk1]; exact one_mem _
    by_cases hkg : g = k
    · rw [←hkg]; exact mem_zpowers g
    rcases quadratic_pair_certificate g (core_in_certificate (hA hg)) k
      (core_in_certificate (hA hk)) hg1 hk1 hkg (quadratic_coordinate A hq g k hg hk) with he | he | he
    · exact (hn (he ▸ hg)).elim
    · exact (hn (he ▸ hk)).elim
    · exact (hn (he ▸ A.mul_mem hg hk)).elim
  let := pointCore_elementary
  have hs : g^2 = 1 := elemPow_eq_one_of_isElementaryAbelian g (hA hg)
  have hcard : Nat.card (zpowers g) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hs)
  have hh := (card_le_of_le hle).trans hcard
  omega

/-- A quadratic subgroup of order at least four in the marked point core contains
its unique transposition. This model calculation also applies to cubic covers. -/
theorem conjugate_four_contains_swap (A : Subgroup S) (u : S)
    (hA : A ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hq : QuadraticPointCore.Quadratic A) (hc : 4 ≤ Nat.card A) : u*swap45*u⁻¹ ∈ A := by
  let B := A.map (MulAut.conj u⁻¹).toMonoidHom
  have hB : B ≤ pointCore := by
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨k,hk,he⟩ := hA hg
    rw [←he]
    simpa [MulAut.conj_apply,mul_assoc] using hk
  have hcard : 4 ≤ Nat.card B := by
    dsimp only [B]
    rw [card_map_of_injective (MulAut.conj u⁻¹).injective]
    exact hc
  obtain ⟨g,hg,he⟩ := quadratic_four_contains_swap B hB
    (QuadraticPointCore.quadratic_conjugate A hq u⁻¹) hcard
  have hh := congrArg (MulAut.conj u) he
  have heq : (MulAut.conj u) ((MulAut.conj u⁻¹) g) = g := by
    simp [MulAut.conj_apply,mul_assoc]
  change (MulAut.conj u) ((MulAut.conj u⁻¹) g) = (MulAut.conj u) swap45 at hh
  rw [heq] at hh
  change g = u*swap45*u⁻¹ at hh
  exact hh ▸ hg

private theorem canonical_core_fixed (g : S) (hg : g ∈ pointCore) :
    coreRepresentation (Fin 6) g (CoreCrossing.pairWord 4 5) = CoreCrossing.pairWord 4 5 := by
  have h : eight.all (fun g => decide
    (coreRepresentation (Fin 6) g (CoreCrossing.pairWord 4 5) = CoreCrossing.pairWord 4 5)) = true := by decide +kernel
  have hh : ∀g∈eight, coreRepresentation (Fin 6) g (CoreCrossing.pairWord 4 5) = CoreCrossing.pairWord 4 5 := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  exact hh g (core_in_certificate hg)

private theorem canonical_natural_fixed (g : S) (hg : g ∈ pointCore) :
    naturalRepresentation (Fin 6) g (pairVector 4 5) = pairVector 4 5 := by
  have hh := congrArg (coreToNatural (Fin 6)) (canonical_core_fixed g hg)
  rw [coreToNatural_equivariant] at hh
  exact hh

private theorem canonical_natural_displacement :
    naturalRepresentation (Fin 6) swap45 (pairVector 0 4)-pairVector 0 4 = pairVector 4 5 := by
  have he : coreRepresentation (Fin 6) swap45 (CoreCrossing.pairWord 0 4)-CoreCrossing.pairWord 0 4 = CoreCrossing.pairWord 4 5 := by decide
  have hh := congrArg (coreToNatural (Fin 6)) he
  rw [map_sub,coreToNatural_equivariant] at hh
  exact hh

private theorem canonical_natural_not_fixed :
    naturalRepresentation (Fin 6) (Equiv.swap 0 4) (pairVector 4 5) ≠ pairVector 4 5 := by
  rw [pairVector_map]
  intro he
  have hh := (pairVector_eq_iff (by decide) (by decide)).mp he
  exact (by decide : pair ((Equiv.swap (0:Fin 6) 4) 4) ((Equiv.swap (0:Fin 6) 4) 5) ≠ pair 4 5) hh

private theorem witness_transport
    {Y W : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) S Y) (τ : Representation (ZMod 2) S W)
    (E : Y ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = τ g (E v))
    (v w : W) (hdisp : τ swap45 v-v = w)
    (hfix : ∀g∈pointCore, τ g w=w) (hn : ∃g, τ g w≠w)
    (u : S) : ∃ z : Y, let r := ρ (u*swap45*u⁻¹) z-z
      (∀g∈pointCore.map (MulAut.conj u).toMonoidHom, ρ g r=r) ∧
      ¬ ∀g, ρ g r=r := by
  let z := E.symm (τ u v)
  have hr : E (ρ (u*swap45*u⁻¹) z-z) = τ u w := by
    rw [map_sub,hE]
    simp only [z,LinearEquiv.apply_symm_apply,map_mul,Module.End.mul_apply,τ.inv_self_apply]
    rw [←map_sub,hdisp]
  refine ⟨z,?_,?_⟩
  · rintro _ ⟨k,hk,rfl⟩
    apply E.injective
    rw [hE,hr]
    change τ (u*k*u⁻¹) (τ u w) = τ u w
    simp only [map_mul,Module.End.mul_apply,τ.inv_self_apply,hfix k hk]
  · intro hall
    obtain ⟨g,hg⟩ := hn
    have hh := congrArg E (hall (u*g*u⁻¹))
    rw [hE,hr] at hh
    have he : τ g w=w := by
      apply (τ.apply_bijective u).injective
      simpa only [map_mul,Module.End.mul_apply,τ.inv_self_apply] using hh
    exact hg he

/-- In either full central cover, the point-core transposition has a noncentral
 displacement fixed by that entire point core, in the same marking. -/
theorem cover_model_fixed_displacement
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (hmodel : SixCover.IsNaturalOrCore ρ (MonoidHom.id _)) (u : S) :
    ∃ z : Y, let r := ρ (u*swap45*u⁻¹) z-z
      (∀g∈pointCore.map (MulAut.conj u).toMonoidHom, ρ g r=r) ∧
      ¬ ∀g, ρ g r=r := by
  rcases hmodel with ⟨E,hE⟩ | ⟨E,hE⟩
  · exact witness_transport ρ (naturalRepresentation (Fin 6)) E
      (by simpa only [MonoidHom.id_apply] using hE)
      (pairVector 0 4) (pairVector 4 5) canonical_natural_displacement
      canonical_natural_fixed ⟨_,canonical_natural_not_fixed⟩ u
  · exact witness_transport ρ (coreRepresentation (Fin 6)) E
      (by simpa only [MonoidHom.id_apply] using hE)
      (CoreCrossing.pairWord 0 4) (CoreCrossing.pairWord 4 5) (by decide)
      canonical_core_fixed ⟨Equiv.swap 0 4,by decide⟩ u

end TerminalLine
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

open scoped IsMulCommutative in
private theorem cover_fixed_displacement (u : S) :
    ∃ z : Additive (replacementMoved d), let r := coverAction s (u*swap45*u⁻¹) z-z
      (∀g∈pointCore.map (MulAut.conj u).toMonoidHom, coverAction s g r=r) ∧
      ¬ ∀g, coverAction s g r=r := by
  rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
  · exact TerminalLine.witness_transport (Y := Additive (replacementMoved d)) (W := natural (Fin 6))
      (coverAction s) (naturalRepresentation (Fin 6)) E (by simpa only [MonoidHom.id_apply] using hE)
      (pairVector 0 4) (pairVector 4 5) TerminalLine.canonical_natural_displacement
      TerminalLine.canonical_natural_fixed ⟨_,TerminalLine.canonical_natural_not_fixed⟩ u
  · exact TerminalLine.witness_transport (Y := Additive (replacementMoved d)) (W := BinaryPermutation.core (Fin 6))
      (coverAction s) (coreRepresentation (Fin 6)) E (by simpa only [MonoidHom.id_apply] using hE)
      (CoreCrossing.pairWord 0 4) (CoreCrossing.pairWord 4 5) (by decide)
      TerminalLine.canonical_core_fixed ⟨Equiv.swap 0 4,by decide⟩ u

/-- The quadratic order-four image supplies a noncentral element of its
actual cover commutator fixed by the whole containing point core. -/
theorem large_point_image_fixed_commutator
    (A T : Subgroup d.overgroup) (hAT : A ≤ T) (u : S)
    (hT : T.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hq : QuadraticPointCore.Quadratic (A.map s.projection))
    (hcard : 4 ≤ Nat.card (A.map s.projection)) :
    ¬ ⁅replacementMoved d,A⁆ ⊓ centralizer (T : Set d.overgroup) ≤ center d.overgroup := by
  have hat := TerminalLine.conjugate_four_contains_swap (A.map s.projection) u
    ((map_mono hAT).trans hT) hq hcard
  obtain ⟨a,ha,hea⟩ := hat
  obtain ⟨v,hfix,hnon⟩ := cover_fixed_displacement s u
  let r := coverAction s (u*swap45*u⁻¹) v-v
  have hr : (r.toMul : d.overgroup) = a*v.toMul*a⁻¹*(v.toMul : d.overgroup)⁻¹ := by
    dsimp only [r]
    rw [toMul_sub,Subgroup.coe_div,div_eq_mul_inv,←hea,coverAction_conjugate]
  have hrA : (r.toMul : d.overgroup) ∈ ⁅replacementMoved d,A⁆ := by
    rw [hr,commutator_comm]
    exact commutator_mem_commutator ha v.toMul.property
  have hrT : (r.toMul : d.overgroup) ∈ centralizer (T : Set d.overgroup) := by
    intro t ht
    have hh := congrArg (fun z : Additive (replacementMoved d) => (z.toMul : d.overgroup))
      (hfix (s.projection t) (hT (mem_map_of_mem _ ht)))
    rw [coverAction_conjugate] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  intro hcentral
  have hc := hcentral ⟨hrA,hrT⟩
  apply hnon
  intro g
  obtain ⟨t,rfl⟩ := s.surjective g
  change (coverAction s (s.projection t) r).toMul = r.toMul
  apply Subtype.ext
  rw [coverAction_conjugate]
  rw [(mem_center_iff.mp hc t),mul_inv_cancel_right]

private theorem critical_first_seed_noncentral_base
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ¬ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ⊓ Z d.radical (p.walk.getVert 1) ≤
      centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  by_cases hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4
  · have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ := by
      let := pointCore_elementary
      let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
      have hEA : IsElementaryAbelian 2 (d.radical.map s.projection) := IsElementaryAbelian.of_le hR
      exact commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff_isMulCommutative.mpr hEA.toIsMulCommutative)
    rw [inf_eq_left.mpr (small_critical_line_le_first_seed_of_abelian_image s hc hab p hsmall)]
    exact critical_commutator_not_central s hc p
  have hp := replacementDistance_pos h d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  let t := p.walk.getVert 1
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hAt : Z d.radical a' ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant _ p.end_color]
    change p.walk.length-1 < replacementDistance h d
    omega
  have htG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  obtain ⟨v,hv⟩ := graphImage_le_pointCore_of_le_edge s u hR t hat (Q d.radical t) le_rfl
  let A := (Z d.radical a').comap (embedM d.radical)
  let T := (Q d.radical t).comap (embedM d.radical)
  have hmA : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((hAt.trans htG).trans_eq (stabilizer_m_base d.radical))
  have hmT : T.map (embedM d.radical) = Q d.radical t :=
    map_comap_eq_self (htG.trans_eq (stabilizer_m_base d.radical))
  have hcard : 4 ≤ Nat.card (A.map s.projection) := by
    change 4 ≤ Nat.card (graphImage s (Z d.radical a'))
    rw [graphImage_card s _ (hAt.trans htG)]
    exact reverse_critical_image_four_le s hc hp p (by omega)
  have hn := large_point_image_fixed_commutator s A T (comap_mono hAt) v hv
    (critical_opposite_image_quadratic s hc p) hcard
  intro hcentral
  apply hn
  rintro x ⟨hx,hxT⟩
  have hxD : embedM d.radical x ∈ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ := by
    have hh := mem_map_of_mem (embedM d.radical) hx
    rw [map_commutator,hmA,←hc.U_eq_moved] at hh
    exact commutator_mono (DistanceEight.U_le_Z d.radical _) le_rfl hh
  have hxZ : embedM d.radical x ∈ Z d.radical (alpha d.radical) :=
    (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)) hxD
  have hxQ : embedM d.radical x ∈ Q d.radical t := by
    apply Q_le_adjacent_h d.radical ht hat
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl) _ hxZ
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ rfl]
    exact hp
  have hxC : embedM d.radical x ∈ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [←hmT]
    exact map_centralizer_le_centralizer_image (T : Set d.overgroup) (embedM d.radical)
      (mem_map_of_mem _ hxT)
  have hxseed : embedM d.radical x ∈ Z d.radical t := by
    rw [Z,if_neg (by simp [ht])]
    let := (replacementGeometry h d).Z_elementary hp (alpha d.radical) rfl
    exact mem_omegaCenter_iff.mpr ⟨hxQ,elemPow_eq_one_of_isElementaryAbelian _ hxZ,hxC⟩
  apply mem_center_iff.mpr
  intro m
  apply embedM_injective d.radical
  simp only [map_mul]
  apply hcentral ⟨hxD,hxseed⟩
  change embedM d.radical m ∈ stabilizer d.radical (mVertex d.radical 1)
  rw [stabilizer_m_base]
  exact ⟨m,rfl⟩


/-- A critical commutator meets its first edge seed in a subgroup that is
noncentral at its own start. This retains the center of the order-32 cover. -/
theorem critical_first_seed_noncentral
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ¬ ⁅Z d.radical a,Z d.radical a'⁆ ⊓ Z d.radical (p.walk.getVert 1) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := critical_first_seed_noncentral_base s hc u hR
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  intro hcentral
  apply base (p.act g⁻¹)
  have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hcentral).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_commutator] at hh
  simpa only [CriticalPath.act,actWalk_getVert,Z_act,stabilizer_act,inv_inv,Subgroup.coe_map] using hh

private theorem terminal_central_fixed_map {F : Type*} [Group F] (H K : Subgroup F)
    (hHK : H ≤ centralizer (K : Set F)) {x : F} (hx : x ∈ K) :
    H.map (MulAut.conj x).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hx))

/-- The same two generating edges and component transporter exclude the
critical configuration for both cover orders. -/
theorem point_image_three_shift_generators_false (hc : DistanceTwo.CentralLayer d)
    (u : S)
    (hfull : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a e : Vertex d.radical} (p : CriticalPath d.radical (replacementGeometry h d) a e)
    (c v z f g : Vertex d.radical)
    (hct : Adjacent d.radical c (p.walk.getVert 1)) (hcv : Adjacent d.radical c v)
    (hgenC : Q d.radical (p.walk.getVert 1)⊔Z d.radical f=stabilizer d.radical c)
    (hgenD : Q d.radical v⊔Z d.radical g=stabilizer d.radical z)
    (hRf : ⁅Z d.radical a,Z d.radical e⁆≤centralizer (Z d.radical f:Set (FreeAmalgam d.radical)))
    (hRg : ⁅Z d.radical a,Z d.radical e⁆≤centralizer (Z d.radical g:Set (FreeAmalgam d.radical)))
    (x : FreeAmalgam d.radical) (hx : x∈stabilizer d.radical c) (hxa : act d.radical x z=a) : False := by
  let H := ⁅Z d.radical a,Z d.radical e⁆⊓Z d.radical (p.walk.getVert 1)
  have hnon := critical_first_seed_noncentral s hc u hfull p
  have ht : color d.radical (p.walk.getVert 1)=true := by
    have hcol := p.vertex_color (show 1≤p.walk.length by
      have hh : 0<p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
      omega)
    have hf : ¬color d.radical (p.walk.getVert 1)=false := by
      intro hh
      have he := hcol.mp hh
      norm_num at he
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hseed (w : Vertex d.radical) (hw : color d.radical w=true) :
      Z d.radical w≤centralizer (Q d.radical w:Set (FreeAmalgam d.radical)) := by
    intro z hz
    rw [Z,if_neg (by simp [hw])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hHC : H≤centralizer (stabilizer d.radical c:Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgenC]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (hseed _ ht)))
      (le_centralizer_iff.mp (inf_le_left.trans hRf))
  have hHv : H≤Z d.radical v := by
    obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors d.radical c hct hcv
    rw [←hyt,Z_act]
    rw [←terminal_central_fixed_map H (stabilizer d.radical c) hHC ((stabilizer d.radical c).inv_mem hy)]
    exact map_mono inf_le_right
  have hc0 : color d.radical c=false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hv : color d.radical v=true := by
    have hh := adjacent_color_ne d.radical hcv
    rw [hc0] at hh
    cases he : color d.radical v <;> simp_all
  have hHD : H≤centralizer (stabilizer d.radical z:Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgenD]
    exact sup_le (le_centralizer_iff.mp (hHv.trans (hseed _ hv)))
      (le_centralizer_iff.mp (inf_le_left.trans hRg))
  have hHA : H≤centralizer (stabilizer d.radical a:Set (FreeAmalgam d.radical)) := by
    rw [←hxa,stabilizer_act]
    have hh := (map_mono (f:=(MulAut.conj x⁻¹).toMonoidHom) hHD).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [terminal_central_fixed_map H (stabilizer d.radical c) hHC ((stabilizer d.radical c).inv_mem hx)] at hh
  exact hnon hHA

/-- The full point-core branch of MS93 (5.11), on the actual minimum
characteristic replacement and with both central covers retained. -/
theorem full_point_distance_le_four_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) : replacementDistance h d ≤ 4 := by
  by_contra! hb
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  obtain ⟨q,r,t,_⟩ := full_point_three_backward_shifts_knownSimple hb u hfull p
  have hq2 : q.path.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hyz : act d.radical r.transporter (alpha d.radical) = r.start := by
    simpa only [hq2] using r.start_eq
  have hlenP : p.walk.length = replacementDistance h d := p.length_eq_b
  have hlenQ : q.path.walk.length = replacementDistance h d := q.path.length_eq_b
  have hdist1 : (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2 := by
    rw [q.path.dist_end]
    omega
  have hdist2 : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hdist : (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2)) a' ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := q.path.walk.getVert (q.path.walk.length-2)) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  have hHe : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hcent (w : Vertex d.radical) (hw : color d.radical w = false)
      (hdist : (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2)) w < replacementDistance h d) :
      ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
        centralizer (Z d.radical w : Set (FreeAmalgam d.radical)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical w hw)))
    rwa [(replacementGeometry h d).distance_constant _ r.path.end_color]
  exact point_image_three_shift_generators_false s hc u hf.le r.path
    q.start q.edge (alpha d.radical) (p.walk.getVert (p.walk.length-2)) a'
    (by rw [r.first]; exact r.adjacent_start) q.adjacent_shift
    (by rw [r.first]; exact r.generation) q.generation
    (hcent _ q.path.end_color (by omega)) (hcent _ p.end_color (by omega))
    r.transporter r.transporter_mem hyz


/-- Positivity and parity leave exactly distances two and four for the
actual full-point characteristic replacement. -/
theorem full_point_distance_two_or_four_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) :
    replacementDistance h d = 2 ∨ replacementDistance h d = 4 := by
  have hb := full_point_distance_le_four_knownSimple u hfull
  have hp := replacementDistance_pos h d
  have he := replacementDistance_even h d
  rw [Nat.even_iff] at he
  omega

/-- Application to the literal chosen minimum replacement. The full-point
case now needs only the separate source-(5.12) exclusion; that premise is
still explicit, and no unconditional Section 5 result is asserted. -/
theorem original_full_point_distance_two_knownSimple_of_four_input
    (hfour : DistanceFourInput.{u} KnownSimple.IsKnownSimple)
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    (u : S)
    (hfull : (replacement h).radical.map
      (SourceReduction.projection h e hz hn (replacement h)) =
        pointCore.map (MulAut.conj u).toMonoidHom) :
    replacementDistance h (replacement h) = 2 := by
  rcases full_point_distance_two_or_four_knownSimple u hfull with hb | hb
  · exact hb
  · have s := fullSymmetricAction_knownSimple h e hz hn (replacement h) (by omega)
    exact (hfour G L R h e hz hn (replacement h) s
      (DistanceTwo.centralLayer_knownSimple G L R h e hz hn (replacement h)) hb).elim

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
