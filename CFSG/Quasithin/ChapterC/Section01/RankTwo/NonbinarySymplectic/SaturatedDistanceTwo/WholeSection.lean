module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.WholeKernel
public import Theory.Representation.SymplecticFourOrthogonalCover.Universal

/-!
# The full two-core above its natural submodule

At distance two, Q/C_Q(L) is a binary section containing the natural module
as a dual cover. The connecting map embeds its quotient by that natural
submodule in H¹ of the natural module, of binary dimension n. Consequently
[Q : U C_Q(L)] is at most q, with the complete fixed attachment retained.

This is the bound r ≤ q used at the beginning of MS93 (3.7), printed p.873.
The construction uses the existing whole-core theorem at arbitrary degree.

For an actual critical Z-image of order q, a centralizer index at most q
on the entire core forces equality Q = U C_Q(L). Four conjugates of the
critical root generate the component, so its full quotient has dimension
at most 4n; the embedded natural module attains this bound. This is the
core-collapse step used in source (3.7)(3), independently of the order of
the replacement radical.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

-- The coordinate argument is the private whole-kernel construction in
-- DistanceTwoRecognition/WholeKernel. Here it is used before restricting
-- the critical image to order q, to obtain the source's general r ≤ q bound.
omit h [Finite H] in
private theorem wholeKernelDualCover_of_marked_cover
    {E J V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (a : Vertex d.radical) (s₀ : MovedSection ρ B)
    (e : ActionEquiv (s₀.action.comp B.subtype) (binaryNatural (K := E)))
    (he : IsCover (MovedSection.coverProjection s₀ e))
    (j : Multiplicative s₀.space.toSubmodule →* FreeAmalgam d.radical)
    (hjr : j.range = U d.radical a)
    (s : WholeKernelQuotient d.radical a J)
    (hκL : ((Ltilde d.radical a).subgroupOf
      (stabilizer d.radical a)).map s.quotient = B)
    (hconj : ∀ (g : stabilizer d.radical a) (v : s₀.space.toSubmodule),
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (s.quotient g) v)) =
        (g : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam d.radical)⁻¹)
    (hker : ∀ v : s₀.space.toSubmodule, MovedSection.coverProjection s₀ e v = 0 ↔
      j (Multiplicative.ofAdd v) ∈
        centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
    (hZQ : Z d.radical a ≤ Q d.radical a)
    (hcomm : ⁅Q d.radical a,Ltilde d.radical a⁆ ≤
      U d.radical a) :
    let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
    ∃ i : (binaryNatural (K := E)).IntertwiningMap (s.action.comp γ),
      Function.Injective i ∧ IsDualCover i.range ∧
      ∀ w, w ∈ i.toLinearMap.range ↔
        ∃ x : Q d.radical a, (x : FreeAmalgam d.radical) ∈
          U d.radical a ∧ (s.sectionData.coordinates x).toAdd = w := by
  let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hγ : γ.range = B := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  let L₀ := Ltilde d.radical a
  let S := stabilizer d.radical a
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  let f₀ : L₀ →* B := (s.quotient.comp (inclusion hLS)).codRestrict B (by
    intro l
    exact hκL.le (mem_map_of_mem s.quotient (show inclusion hLS l ∈ L₀.subgroupOf S from l.property)))
  have hf₀ : Function.Surjective f₀ := by
    intro c
    obtain ⟨l,hl,he⟩ := (hκL.symm ▸ c.property : c.val ∈ (L₀.subgroupOf S).map s.quotient)
    exact ⟨⟨l.val,hl⟩,Subtype.ext he⟩
  let f := e.groupEquiv.toMonoidHom.comp f₀
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp hf₀
  have hγf (l : L₀) : γ (f l) = s.quotient (inclusion hLS l) := by
    change (e.groupEquiv.symm (e.groupEquiv (f₀ l)) : J) = _
    rw [e.groupEquiv.symm_apply_apply]
    rfl
  let σ := s.action.comp γ
  let π := s.sectionData.coordinates
  have hUA : U d.radical a ≤ Q d.radical a :=
    (U_le_Z _).trans hZQ
  have hLA : L₀ ≤ normalizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    hLS.trans (Q_normalized _ _)
  have hact (l : L₀) (a : Q d.radical a) :
      (π ⟨(l : FreeAmalgam d.radical)*a*(l : FreeAmalgam d.radical)⁻¹,
        (mem_normalizer_iff.mp (hLA l.property) a).mp a.property⟩).toAdd =
          σ (f l) (π a).toAdd := by
    change _ = s.action (γ (f l)) (π a).toAdd
    rw [hγf]
    exact s.sectionData.equivariant (inclusion hLS l) a
  have hjact (l : L₀) (v : s₀.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s₀ e (f l) v)) =
        (l : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(l : FreeAmalgam d.radical)⁻¹ := by
    change j (Multiplicative.ofAdd (s₀.space.toRepresentation (γ (f l)) v)) = _
    rw [hγf]
    exact hconj (inclusion hLS l) v
  have hkernel (v : s₀.space.toSubmodule) : MovedSection.coverProjection s₀ e v = 0 ↔
      π ⟨j (Multiplicative.ofAdd v),hUA (hjr ▸ ⟨Multiplicative.ofAdd v,rfl⟩)⟩ = 1 := by
    have hvU : j (Multiplicative.ofAdd v) ∈ U d.radical a :=
      hjr ▸ ⟨Multiplicative.ofAdd v,rfl⟩
    have hvQ : j (Multiplicative.ofAdd v) ∈ Q d.radical a :=
      hUA hvU
    apply (hker v).trans
    exact (show (j (Multiplicative.ofAdd v) ∈ centralizer (L₀ : Set (FreeAmalgam d.radical))) ↔
      j (Multiplicative.ofAdd v) ∈ Q d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      from ⟨fun hv => ⟨hUA hvU,hv⟩,fun hv => hv.2⟩).trans
      (s.sectionData.coordinates_eq_one_iff ⟨j (Multiplicative.ofAdd v),hUA hvU⟩).symm
  have hmap : ((Ltilde d.radical a).subgroupOf S).map s.quotient = B := by
    exact hκL
  have hfixed : OneCohomology.fixed σ = ⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    intro c
    have hc : c.val ∈ B := hmap.le c.property
    obtain ⟨g,hg⟩ := (hγ.symm ▸ hc : c.val ∈ γ.range)
    change s.action c.val v = v
    rw [←hg]
    exact hv g
  obtain ⟨i,hi,hdual,_,hrange⟩ := exists_dualCover_of_conjugation_section
    (Q d.radical a) (U d.radical a) L₀ hUA hLA
    hcomm
    (MovedSection.coverAction s₀ e) σ (binaryNatural (K := E))
    (MovedSection.coverProjection s₀ e) he.1 j hjr π s.sectionData.onto f hf hjact hact hkernel hfixed
  exact ⟨i,hi,hdual,hrange⟩


omit h d [Finite H] in
private theorem natural_dualCover_quotient_bound
    {E W : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (i : (binaryNatural (K := E)).IntertwiningMap σ)
    (hi : Function.Injective i) (hd : IsDualCover i.range) :
    Module.finrank (ZMod 2) (W ⧸ i.toLinearMap.range) ≤ Module.finrank (ZMod 2) E := by
  have hr := LinearMap.finrank_le_finrank_of_injective
    (quotientToH1_injective i.range hd.1 hd.2)
  let e := LinearEquiv.ofInjective i.toLinearMap hi
  have he : ∀ g v, e ((binaryNatural (K := E)) g v) = i.range.toRepresentation g (e v) := by
    intro g v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining (binaryNatural (K := E)) σ i g v
  let ec := H1Congr (binaryNatural (K := E)) i.range.toRepresentation (MulEquiv.refl _) e he
  rw [←ec.finrank_eq,finrank_restrictScalars,Representation.OneCohomology.SymplecticFour.finrank_H1_eq_one,
    mul_one] at hr
  exact hr

include h

/-- The entire core modulo its full fixed part contains a natural dual cover
with at most one additional field dimension. This is available before a
field-sized critical pair has been selected. -/
theorem wholeKernel_natural_dualCover
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    ∃ (E : BinaryField), E.degree = n ∧
      ∃ (s : WholeKernelQuotient d.radical a (d.overgroup ⧸ pCore 2 d.overgroup))
        (γ : L (K := E.Carrier) →* (d.overgroup ⧸ pCore 2 d.overgroup)),
        γ.range = replacementComponent d ∧
        ∃ i : (binaryNatural (K := E.Carrier)).IntertwiningMap (s.action.comp γ),
          Function.Injective i ∧ IsDualCover i.range ∧
          (∀ w, w ∈ i.toLinearMap.range ↔
            ∃ x : Q d.radical a, (x : FreeAmalgam d.radical) ∈ U d.radical a ∧
              (s.sectionData.coordinates x).toAdd = w) ∧
          Module.finrank (ZMod 2) (s.Carrier ⧸ i.toLinearMap.range) ≤ n := by
  let := replacementComponent_normal h d
  let s₀ := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d ha
  obtain ⟨s,hs⟩ := replacement_wholeKernelQuotient_over h d g hb ha κ hκ hκQ
  let γ := (replacementComponent d).subtype.comp e.groupEquiv.symm.toMonoidHom
  have hZQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a ha (by
      rw [g.distance_constant a ha]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  obtain ⟨i,hi,hd,hrange⟩ := wholeKernelDualCover_of_marked_cover d a s₀ e he j hjr s
    (by rw [hs]; exact hκL) (by intro x v; rw [hs]; exact hconj x v) hker hZQ
    (replacement_core_eq_U_of_distance_two h d g hb ha).le
  refine ⟨E,hE,s,γ,?_,i,hi,hd,hrange,?_⟩
  · rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  · have hr := natural_dualCover_quotient_bound (s.action.comp γ) i hi hd
    have hdegree : Module.finrank (ZMod 2) E.Carrier = n := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E.Carrier)
      rw [Nat.card_zmod,E.card_eq,hE] at hc
      exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
    rwa [hdegree] at hr

/-- The literal full-core index bound r ≤ q from MS93 (3.7), p.873.
The denominator contains the entire fixed attachment, not just its involutions. -/
theorem core_relIndex_natural_sup_fixed_le
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    (U d.radical a ⊔ fixedCore d.radical a).relIndex (Q d.radical a) ≤ 2^n := by
  obtain ⟨E,hE,s,γ,hγ,i,hi,hd,hrange,hrank⟩ :=
    wholeKernel_natural_dualCover h d g hb ha
  let V := i.toLinearMap.range
  let π := s.sectionData.coordinates
  let f : Q d.radical a →* Multiplicative (s.Carrier ⧸ V) :=
    V.mkQ.toAddMonoidHom.toMultiplicative.comp π
  have hf : Function.Surjective f := V.mkQ_surjective.comp s.sectionData.onto
  have hV : V.toAddSubgroup.toSubgroup =
      ((U d.radical a).subgroupOf (Q d.radical a)).map π := by
    ext w
    change w.toAdd ∈ i.toLinearMap.range ↔ _
    rw [hrange]
    constructor
    · rintro ⟨x,hx,he⟩
      exact ⟨x,hx,Multiplicative.toAdd.injective he⟩
    · rintro ⟨x,hx,he⟩
      exact ⟨x,hx,congrArg Multiplicative.toAdd he⟩
  have hk : f.ker = (V.toAddSubgroup.toSubgroup).comap π := by
    ext x
    change V.mkQ (π x).toAdd = 0 ↔ (π x).toAdd ∈ V
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  have hUQ : U d.radical a ≤ Q d.radical a := by
    apply (U_le_Z _).trans
    exact (g.omega_bound a ha (by
      rw [g.distance_constant a ha]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hkernel : f.ker.map (Q d.radical a).subtype =
      U d.radical a ⊔ fixedCore d.radical a := by
    rw [hk,hV,comap_map_eq,Subgroup.map_sup,s.sectionData.kernel_eq,
      map_subgroupOf_eq_of_le hUQ,map_subgroupOf_eq_of_le s.sectionData.kernel_le]
    rfl
  have hindex : (U d.radical a ⊔ fixedCore d.radical a).relIndex (Q d.radical a) =
      Nat.card (s.Carrier ⧸ V) := by
    rw [←hkernel]
    have hh := relIndex_map_map_of_injective (f := (Q d.radical a).subtype)
      f.ker ⊤ (Q d.radical a).subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,relIndex_top_right,index_ker,
      MonoidHom.range_eq_top.mpr hf,Nat.card_congr (topEquiv : (⊤ : Subgroup (Multiplicative (s.Carrier ⧸ V))) ≃* _).toEquiv] at hh
    exact hh
  rw [hindex,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hrank


omit h d in
private theorem section_fixedCodim_le_centralizer_index
    {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    (S A D B : Subgroup G) [Finite A]
    (κ : S →* J) (σ : Representation (ZMod 2) J W)
    (c : BinaryConjugationSection S A D (σ.comp κ))
    (hDS : S ≤ normalizer (D : Set G)) (hBS : B ≤ S) :
    2 ^ fixedCodim σ ((B.subgroupOf S).map κ) ≤
      (centralizer (B : Set G)).relIndex A := by
  have hi := c.fixed_index_of_relative_normalizers B hBS
    (c.section_le.trans hDS) (hBS.trans hDS)
  unfold fixedCodim at hi ⊢
  rw [fixedSpace_comp_map] at hi
  rw [←hi,←inf_relIndex_right (centralizer (B : Set G)) A]
  apply relIndex_le_of_le_left
  · apply le_commutatorPreimage inf_le_right
    rw [commutator_eq_bot_iff_le_centralizer.mpr inf_le_left]
    exact bot_le
  · exact index_ne_zero_of_finite

/-- The four-root argument on the whole core for an actual field-sized
critical Z-image. The centralizer bound is on Q itself and the denominator
retains the entire component-fixed attachment. No order of the replacement
radical is assumed. This is the core-collapse step in MS93 (3.7)(3). -/
theorem core_eq_moving_sup_fixed_of_critical_centralizer_index
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hindex : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (Q d.radical a) ≤ 2^n) :
    Q d.radical a = U d.radical a ⊔ fixedCore d.radical a := by
  let := replacementComponent_normal h d
  let s₀ := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  obtain ⟨s,hs⟩ := replacement_wholeKernelQuotient_over h d g hb path.start_color κ hκ hκQ
  let B := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  let γ := B.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hZQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  obtain ⟨i,hi,hdual,hrange⟩ := wholeKernelDualCover_of_marked_cover d a s₀ e he j hjr s
    (by rw [hs]; exact hκL) (by intro x v; rw [hs]; exact hconj x v) hker hZQ
    (replacement_core_eq_U_of_distance_two h d g hb path.start_color).le
  let σ := s.action.comp γ
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2 := by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith
  obtain ⟨haq,hzq⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega) hsmall
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z d.radical z, ∀ v : s₀.space.toSubmodule,
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s₀ e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hmap : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map κ = β.range.map γ := by
    have heq : γ.comp β = δ := by
      ext x
      exact hβmark x
    rw [←MonoidHom.range_comp,heq]
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
    · rintro y ⟨x,rfl⟩
      exact ⟨inclusion hZA x,x.property,rfl⟩
  have hSN : stabilizer d.radical a ≤ normalizer
      ((Q d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    have hSL : stabilizer d.radical a ≤ normalizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
      have ht := le_normalizer_map (H := pResidual 2 (stabilizer d.radical a))
        (stabilizer d.radical a).subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
      exact ht
    exact (le_inf (Q_normalized d.radical a)
      (hSL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hbound : fixedCodim σ β.range ≤ Module.finrank (ZMod 2) E.Carrier := by
    have hi := section_fixedCodim_le_centralizer_index (stabilizer d.radical a)
      (Q d.radical a) _ (Z d.radical z) s.quotient s.action s.sectionData hSN hZA
    rw [hs,hmap] at hi
    have hie : fixedCodim s.action (β.range.map γ) = fixedCodim σ β.range := by
      have he : fixedSpace σ β.range = fixedSpace s.action (β.range.map γ) := by
        ext v
        constructor
        · intro hv a
          obtain ⟨x,hx,he⟩ := a.property
          change s.action a.val v = v
          rw [←he]
          exact hv ⟨x,hx⟩
        · intro hv a
          exact hv ⟨γ a.val,mem_map_of_mem γ a.property⟩
      exact congrArg (fun A : Submodule (ZMod 2) s.Carrier =>
        Module.finrank (ZMod 2) (s.Carrier ⧸ A)) he.symm
    rw [hie] at hi
    have hdegree : Module.finrank (ZMod 2) E.Carrier = n := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E.Carrier)
      rw [Nat.card_zmod,hFc] at hc
      exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
    rw [hdegree]
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hi.trans hindex)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨f,hf⟩ := derived_four_conjugates_of_displacement_one hcard β.range hβcard hβdim hβquad
  have hdim := fixedCodim_le_card_mul_of_subgroup_conjugates σ ⊤ β.range f hf.ge
  have hfixed : fixedSpace σ ⊤ = ⊥ := by
    apply bot_unique
    intro v hv
    exact hdual.2.le (fun x => hv ⟨x,mem_top _⟩)
  have htotal := fixedCodim_add_finrank σ ⊤
  rw [hfixed,finrank_bot,add_zero] at htotal
  rw [htotal,Fintype.card_fin] at hdim
  have htotalBound : Module.finrank (ZMod 2) s.Carrier ≤ 4 * Module.finrank (ZMod 2) E.Carrier :=
    hdim.trans (Nat.mul_le_mul_left 4 hbound)
  have hdimI : Module.finrank (ZMod 2) i.toLinearMap.range =
      4 * Module.finrank (ZMod 2) E.Carrier := by
    rw [LinearMap.finrank_range_of_inj hi]
    simp [Natural,Module.finrank_pi_fintype]
  have hfull : i.toLinearMap.range = ⊤ := Submodule.eq_top_of_finrank_eq
    (le_antisymm i.toLinearMap.range.finrank_le (htotalBound.trans_eq hdimI.symm))
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans hZQ
  apply le_antisymm
  · intro x hx
    obtain ⟨u,hu,heq⟩ := (hrange (s.sectionData.coordinates ⟨x,hx⟩).toAdd).mp
      (hfull.symm ▸ Submodule.mem_top)
    have hc : (u⁻¹ * ⟨x,hx⟩ : Q d.radical a) ∈ s.sectionData.coordinates.ker := by
      change s.sectionData.coordinates (u⁻¹ * ⟨x,hx⟩) = 1
      rw [map_mul,map_inv,Multiplicative.toAdd.injective heq,inv_mul_cancel]
    rw [s.sectionData.kernel_eq] at hc
    have he : x = u.val * (u.val⁻¹*x) := by simp
    rw [he]
    exact mul_mem (mem_sup_left hu) (mem_sup_right hc)
  · exact sup_le hUQ inf_le_left

/-- The whole core centralizer of an actual critical layer lies in the
natural core times its complete component-fixed attachment. -/
theorem critical_core_centralizer_le_moving_sup_fixed
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2) :
    Q d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) ≤
      U d.radical z ⊔ fixedCore d.radical z := by
  let := replacementComponent_normal h d
  let s₀ := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  obtain ⟨s,hs⟩ := replacement_wholeKernelQuotient_over h d g hb path.end_color κ hκ hκQ
  let γ := (replacementComponent d).subtype.comp e.groupEquiv.symm.toMonoidHom
  have hZQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  obtain ⟨i,hi,hd,hrange⟩ := wholeKernelDualCover_of_marked_cover d z s₀ e he j hjr s
    (by rw [hs]; exact hκL) (by intro x v; rw [hs]; exact hconj x v) hker hZQ
    (replacement_core_eq_U_of_distance_two h d g hb path.end_color).le
  obtain ⟨β,hβ,hno⟩ := h.replacement_refinement_free_inner_actor d
    (by rw [E.card_eq,hE,h.field_card]) path (by omega) s₀ e he
    (replacement_component_image_structure h d).2.2.2.2 j hj hjr κ hκQ hconj
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  intro x hx
  let xQ : Q d.radical z := ⟨x,hx.1⟩
  have hfix : (s.sectionData.coordinates xQ).toAdd ∈
      OneCohomology.fixed ((s.action.comp γ).comp β.range.subtype) := by
    rintro ⟨b,⟨y,rfl⟩⟩
    change s.action (γ (β y)) (s.sectionData.coordinates xQ).toAdd = _
    have hγy : γ (β y)=s.quotient ⟨y,hAS y.property⟩ := by
      rw [hs]
      exact hβ y (hAS y.property)
    rw [hγy]
    have heq := s.sectionData.equivariant ⟨y,hAS y.property⟩ xQ
    change (s.sectionData.coordinates ⟨y.val*x*y.val⁻¹,_⟩).toAdd =
      s.action (s.quotient ⟨y,hAS y.property⟩) (s.sectionData.coordinates xQ).toAdd at heq
    rw [←heq]
    congr 2
    apply Subtype.ext
    change y.val*x*y.val⁻¹=x
    rw [hx.2 y.val y.property,mul_inv_cancel_right]
  have hmem := dualCover_fixed_le_natural_of_no_refinement i hi hd β.range hno hfix
  obtain ⟨u,hu,heu⟩ := (hrange _).mp hmem
  have hdiff : (u⁻¹*xQ : Q d.radical z) ∈ s.sectionData.coordinates.ker := by
    change s.sectionData.coordinates (u⁻¹*xQ)=1
    rw [map_mul,map_inv,Multiplicative.toAdd.injective heu,inv_mul_cancel]
  rw [s.sectionData.kernel_eq] at hdiff
  have hh := (U d.radical z ⊔ fixedCore d.radical z).mul_mem
    (mem_sup_left hu) (mem_sup_right hdiff)
  change u.val*(u.val⁻¹*x) ∈ U d.radical z ⊔ fixedCore d.radical z at hh
  simpa only [mul_inv_cancel_left] using hh


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
