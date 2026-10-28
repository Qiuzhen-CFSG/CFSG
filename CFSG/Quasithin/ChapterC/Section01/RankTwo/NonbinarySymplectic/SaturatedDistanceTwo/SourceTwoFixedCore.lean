module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoLarge
public import Theory.Representation.SymplecticFourOrthogonalCover.DisplacementLifting

/-!
# The full fixed-core quadraticity contradiction in MS93 (3.7)(2)

Let D = C_Q(L), q = 2ⁿ and r = [Q : UD]. The literal whole-core section
contains the natural four-space, so [Q : D] = q⁴r. Four conjugates of an
actual critical root generate the component and give [Q : D] ≤ k⁴, where
k is its fixed index on Q/D. Since 1 ≤ r ≤ q, necessarily r < k.

If the opposite fixed core moves more than q² cosets on the natural cover,
symplectic orthogonality makes its natural fixed space a line. The critical
commutator fills this line, and lifting through the full covering kernel
places the component-radical intersection in U D′. The previously proved
factorization T₀ = U (T₀ ∩ Q′) then bounds the opposite quotient's fixed
index by r′, contradicting the four-root inequality there.

Thus the entire fixed core moves at most q² cosets and acts quadratically
on U′. The common edge center in Z′ = U′ Z_t is fixed, giving
[Z′, D, D] = 1 on the full original layer. All subgroups, quotient kernels
and actor maps remain those of the original critical configuration.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(2), printed p.873, using (1.1)(ii)(1). The later whole-core
index estimates, midpoint containment in the large-movement case, and field
restriction remain separate source arguments.
-/

public noncomputable section
open scoped commutatorElement IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
private theorem cover_moving_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    (centralizer (A : Set G)).relIndex U =
      Nat.card F ^ Module.finrank F
        (displacementSpace ((commutator (Sp F)).subtype.comp β).range) := by
  let α := (commutator (Sp F)).subtype.comp β
  have hi := embedded_centralizer_index σ U A j hj hjr β hact
  rw [fixedCodim_of_binaryCover p hp] at hi
  have hfixed : fixedSpace (binaryNatural (K := F)) β.range =
      (TwoLocalCover.fixedSpace α.range).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨a,rfl⟩ := hx
      exact hv ⟨β a,⟨a,rfl⟩⟩
    · intro hv x
      obtain ⟨a,ha⟩ := x.property
      change binaryNatural x.val v=v
      rw [←ha]
      exact hv (α a) ⟨a,rfl⟩
  rw [hi]
  change 2 ^ Module.finrank (ZMod 2)
    (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
  rw [hfixed]
  have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
    (TwoLocalCover.fixedSpace α.range)).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  rw [hc,fixed_quotient_card]

private theorem cover_large_centralizer_le
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A B V D : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F)) (γ : B →* L (K := F))
    (hactA : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hactB : ∀ (b : B) (w : W), j (Multiplicative.ofAdd (σ (γ b) w))=
      b.val*j (Multiplicative.ofAdd w)*b.val⁻¹)
    (hlarge : Nat.card F^2 < (centralizer (A : Set G)).relIndex U)
    (hB : 1 < Nat.card (((commutator (Sp F)).subtype.comp γ).range))
    (htriple : ⁅⁅U,B⁆,A⁆=⊥) (hmove : ⁅B,U⁆ ≤ V)
    (hker : ∀ w : W, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ D)
    (hUD : U ≤ normalizer (D : Set G)) :
    commutatorPreimage U A D ≤ V ⊔ D := by
  let α := (commutator (Sp F)).subtype.comp β
  let δ := (commutator (Sp F)).subtype.comp γ
  have hBF : displacementSpace δ.range ≤ TwoLocalCover.fixedSpace α.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩ b hb
    change b • (a.val • v-v)=a.val • v-v
    obtain ⟨a,ha⟩ := a.property
    rw [←ha]
    obtain ⟨b,rfl⟩ := hb
    obtain ⟨w,rfl⟩ := hp.1 v
    have hval : j (Multiplicative.ofAdd (σ (γ a) w-w)) =
        ⁅a.val,j (Multiplicative.ofAdd w)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hactB]
      rfl
    have hc : b.val*⁅a.val,j (Multiplicative.ofAdd w)⁆ =
        ⁅a.val,j (Multiplicative.ofAdd w)⁆*b.val := by
      apply commutator_eq_bot_iff_le_centralizer.mp htriple
      · rw [commutator_comm]
        exact commutator_mem_commutator a.property (hjr ▸ ⟨_,rfl⟩)
      · exact b.property
    have he : σ (β b) (σ (γ a) w-w)=σ (γ a) w-w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hactA,hval,hc,mul_inv_cancel_right]
    have hh := congrArg p he
    rw [p.isIntertwining,map_sub,p.isIntertwining] at hh
    exact hh
  rw [cover_moving_index σ p hp U A j hj hjr β hactA] at hlarge
  have hdim : 2 < Module.finrank F (displacementSpace α.range) :=
    (pow_lt_pow_iff_right₀ (Finite.one_lt_card : 1 < Nat.card F)).mp hlarge
  have hfixed : Module.finrank F (TwoLocalCover.fixedSpace α.range) ≤ 1 := by
    have he := LinearMap.BilinForm.finrank_orthogonal
      (W := displacementSpace α.range) TwoLocalCover.form_nondegenerate
    rw [orthogonal_displacementSpace] at he
    have hv : Module.finrank F (Theory.SpecificGroups.SymplecticFour.Vector F)=4 := by
      simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hv] at he
    omega
  have hBpos : 0 < Module.finrank F (displacementSpace δ.range) := by
    have hh := card_actor_le_displacement_dimension δ.range
    by_contra! hz
    have he : Module.finrank F (displacementSpace δ.range)=0 := by omega
    rw [he,Nat.zero_pow (by decide : 0 < 2),pow_zero] at hh
    exact (not_le_of_gt hB) hh
  have heq : displacementSpace δ.range = TwoLocalCover.fixedSpace α.range :=
    Submodule.eq_of_le_of_finrank_le hBF (by omega)
  intro x hx
  obtain ⟨w,rfl⟩ := (hjr.symm ▸ commutatorPreimage_le U A D hx : x ∈ j.range)
  have hfix : p w.toAdd ∈ TwoLocalCover.fixedSpace α.range := by
    intro a ha
    obtain ⟨a,rfl⟩ := ha
    have hcomm : ⁅a.val,j w⁆ ∈ D := by
      have hh := commutator_commutatorPreimage_le U A D hUD
      rw [commutator_comm] at hh
      exact hh (commutator_mem_commutator a.property hx)
    have hv : j (Multiplicative.ofAdd (σ (β a) w.toAdd-w.toAdd)) = ⁅a.val,j w⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hactA]
      rfl
    have hh := (hker _).mpr (hv.symm ▸ hcomm)
    rw [map_sub,p.isIntertwining,sub_eq_zero] at hh
    exact hh
  obtain ⟨v,hv,hvB⟩ := natural_displacement_lifts U B j hjr γ σ hactB p hp.1
    (p w.toAdd) (heq.symm ▸ hfix)
  have hk : j (Multiplicative.ofAdd (w.toAdd-v)) ∈ D :=
    (hker _).mp (by rw [map_sub,hv,sub_self])
  have hh := (V ⊔ D).mul_mem (mem_sup_left (hmove hvB)) (mem_sup_right hk)
  rw [←map_mul,←ofAdd_add,show v+(w.toAdd-v)=w.toAdd by abel,ofAdd_toAdd] at hh
  exact hh

private theorem fixed_index_le_of_component_intersection
    {G : Type*} [Group G] (T B Q Q' U U' D' Z : Subgroup G) [Finite T]
    (hgen : B ⊔ Q = T) (hB : B = U ⊔ (B ⊓ Q'))
    (hUQ : U ≤ Q) (hQ'T : Q' ≤ T) (_hU'Q' : U' ≤ Q') (hD'Q' : D' ≤ Q')
    (hQT : T ≤ normalizer (Q : Set G)) (hD'T : T ≤ normalizer (D' : Set G))
    (hZT : Z ≤ T) (hQZ : ⁅Q,Z⁆ = ⊥)
    (hinter : B ⊓ (U' ⊔ D') ≤ Q ⊔ D') :
    (commutatorPreimage Q' Z D').relIndex Q' ≤ (U' ⊔ D').relIndex Q' := by
  have hBT : B ≤ T := le_sup_left.trans_eq hgen
  have hQle : Q ≤ T := le_sup_right.trans_eq hgen
  have hDle : D' ≤ T := hD'Q'.trans hQ'T
  let N := Q ⊔ D'
  have hNT : N ≤ T := sup_le hQle hDle
  have hNN : T ≤ normalizer (N : Set G) :=
    (le_inf hQT hD'T).trans (normalizer_inf_normalizer_le_normalizer_sup Q D')
  let : (N.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hNN
  have hjoin : (B ⊓ Q') ⊔ N = T := by
    apply le_antisymm (sup_le (inf_le_left.trans hBT) hNT)
    have hBjoin : B ≤ (B ⊓ Q') ⊔ N := hB.le.trans
      (sup_le (hUQ.trans (le_sup_left.trans le_sup_right)) le_sup_left)
    exact hgen.symm.le.trans (sup_le hBjoin (le_sup_left.trans le_sup_right))
  have hindex : N.relIndex T = N.relIndex (B ⊓ Q') := by
    rw [←relIndex_subgroupOf (show T ≤ T from le_rfl),subgroupOf_self,
      ←show ((B ⊓ Q').subgroupOf T) ⊔ N.subgroupOf T = ⊤ by
        rw [←subgroupOf_sup (inf_le_left.trans hBT) hNT,hjoin,subgroupOf_self],
      relIndex_sup_right,relIndex_subgroupOf (inf_le_left.trans hBT)]
  have hfinite : Finite Q' := Finite.of_injective (inclusion hQ'T) (inclusion_injective _)
  let := hfinite
  let : Finite (B ⊓ Q' : Subgroup G) := Finite.of_injective
    (inclusion (show B ⊓ Q' ≤ Q' from inf_le_right)) (inclusion_injective _)
  have hC : Q' ⊓ N ≤ commutatorPreimage Q' Z D' := by
    apply le_commutatorPreimage inf_le_left
    apply (commutator_mono inf_le_right le_rfl).trans
    apply commutator_sup_le_of_relative_normal T Q D' Z D' hD'T hQle hDle
    · rw [hQZ]; exact bot_le
    · exact le_normalizer_iff_commutator_le_left.mp (hZT.trans hD'T)
  calc
    _ ≤ (Q' ⊓ N).relIndex Q' := relIndex_le_of_le_left hC index_ne_zero_of_finite
    _ = N.relIndex Q' := inf_relIndex_left _ _
    _ ≤ N.relIndex T := relIndex_le_of_le_right hQ'T index_ne_zero_of_finite
    _ = N.relIndex (B ⊓ Q') := hindex
    _ ≤ (U' ⊔ D').relIndex (B ⊓ Q') := by
      rw [←inf_relIndex_right N (B ⊓ Q'),←inf_relIndex_right (U' ⊔ D') (B ⊓ Q')]
      apply relIndex_le_of_le_left ?_ index_ne_zero_of_finite
      exact fun x hx => ⟨hinter ⟨hx.2.1,hx.1⟩,hx.2⟩
    _ ≤ (U' ⊔ D').relIndex Q' := relIndex_le_of_le_right inf_le_right index_ne_zero_of_finite

private theorem component_intersection_le_of_fixed_preimage
    {G : Type*} [Group G] (T B A U V D : Subgroup G)
    (hBT : B ≤ T) (hUT : U ≤ T) (hDT : D ≤ T)
    (hDA : ⁅D,A⁆ ≤ D) (hTD : T ≤ normalizer (D : Set G))
    (hBA : ⁅B,A⁆ = ⊥)
    (hfixed : commutatorPreimage U A D ≤ V ⊔ D) :
    B ⊓ (U ⊔ D) ≤ V ⊔ D := by
  let C := commutatorPreimage T A D
  have hBC : B ≤ C := le_commutatorPreimage hBT (hBA ▸ bot_le)
  have hDC : D ≤ C := le_commutatorPreimage hDT hDA
  have hUC : U ⊓ C ≤ commutatorPreimage U A D :=
    le_commutatorPreimage inf_le_left ((commutator_mono inf_le_right le_rfl).trans
      (commutator_commutatorPreimage_le T A D hTD))
  rintro x ⟨hx,hxu⟩
  change x ∈ U ⊔ D at hxu
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right U D (hUT.trans hTD)] at hxu
  obtain ⟨u,hu,d,hd,rfl⟩ := hxu
  have huC : u ∈ C := by
    have hh := C.mul_mem (hBC hx) (C.inv_mem (hDC hd))
    simpa only [mul_inv_cancel_right] using hh
  exact (V ⊔ D).mul_mem (hfixed (hUC ⟨hu,huC⟩)) (mem_sup_right hd)

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Four actual critical-root conjugates bound the full quotient Q/D by
the fourth power of its quotient centralizer index. -/
theorem core_fixed_index_le_critical_index_pow_four
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    (fixedCore d.radical a).relIndex (Q d.radical a) ≤
      ((commutatorPreimage (Q d.radical a) (Z d.radical z)
        (fixedCore d.radical a)).relIndex (Q d.radical a))^4 := by
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
  have hfixed : fixedSpace σ ⊤ = ⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    rintro ⟨x,hx⟩
    rw [hs,hκL] at hx
    obtain ⟨b,hb⟩ := (e.groupEquiv.symm.surjective ⟨x,hx⟩)
    have he : γ b = x := congrArg Subtype.val hb
    change s.action x v = v
    rw [←he]
    exact hv ⟨b,mem_top _⟩
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨f,hf⟩ := derived_four_conjugates_of_displacement_one hcard β.range hβcard hβdim hβquad
  have hdim := fixedCodim_le_card_mul_of_subgroup_conjugates σ ⊤ β.range f hf.ge
  have htotal := fixedCodim_add_finrank σ ⊤
  rw [hfixed,finrank_bot,add_zero] at htotal
  rw [htotal,Fintype.card_fin] at hdim
  have hindex := s.sectionData.fixed_index_of_relative_normalizers (Z d.radical z)
    hZA (s.sectionData.section_le.trans hSN) (hZA.trans hSN)
  unfold fixedCodim at hindex
  rw [fixedSpace_comp_map,hs,hmap,←fixedSpace_comp_map] at hindex
  change (commutatorPreimage (Q d.radical a) (Z d.radical z)
    (fixedCore d.radical a)).relIndex (Q d.radical a) = 2^fixedCodim σ β.range at hindex
  have horder : (fixedCore d.radical a).relIndex (Q d.radical a) = Nat.card s.Carrier := by
    change ((fixedCore d.radical a).subgroupOf (Q d.radical a)).index = _
    have hk : s.sectionData.coordinates.ker =
        (fixedCore d.radical a).subgroupOf (Q d.radical a) := s.sectionData.kernel_eq
    rw [←hk,index_ker,MonoidHom.range_eq_top.mpr s.sectionData.onto,
      card_top]
    rfl
  rw [horder,hindex,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm] using hdim)

/-- The natural four-space computes the exact size of the full core modulo
its component centralizer, including the extra dual-cover quotient. -/
theorem core_fixed_index_eq_natural_mul
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    (fixedCore d.radical a).relIndex (Q d.radical a) = (2^n)^4 *
      (U d.radical a ⊔ fixedCore d.radical a).relIndex (Q d.radical a) := by
  obtain ⟨E,hE,s,γ,hγ,i,hi,hd,hrange,hrank⟩ := wholeKernel_natural_dualCover h d g hb ha
  have hUQ : U d.radical a ≤ Q d.radical a :=
    (U_le_Z a).trans ((g.omega_bound a ha (by
      rw [g.distance_constant a ha]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _))
  have himage : s.sectionData.imageSpace (U d.radical a) = i.toLinearMap.range := by
    ext w
    rw [hrange,s.sectionData.mem_imageSpace_iff]
  have hiU : (fixedCore d.radical a).relIndex (U d.radical a) = (2^n)^4 := by
    have hic : Nat.card (s.sectionData.imageSpace (U d.radical a)) =
        (fixedCore d.radical a).relIndex (U d.radical a) :=
      s.sectionData.imageSpace_card_eq_relIndex (U d.radical a) hUQ
    rw [←hic,himage,
      ←Nat.card_congr (LinearEquiv.ofInjective i.toLinearMap hi).toEquiv]
    rw [Module.natCard_eq_pow_finrank (K := E.Carrier)]
    simp [Natural,E.card_eq,hE]
  let : ((fixedCore d.radical a).subgroupOf (Q d.radical a)).Normal :=
    s.sectionData.kernel_normal
  have hiUD : (fixedCore d.radical a).relIndex (U d.radical a ⊔ fixedCore d.radical a) = (2^n)^4 := by
    rw [←relIndex_subgroupOf (sup_le hUQ (show fixedCore d.radical a ≤ Q d.radical a from inf_le_left)),
      subgroupOf_sup hUQ (show fixedCore d.radical a ≤ Q d.radical a from inf_le_left),relIndex_sup_right,relIndex_subgroupOf hUQ,hiU]
  exact (relIndex_mul_relIndex (fixedCore d.radical a)
    (U d.radical a ⊔ fixedCore d.radical a) (Q d.radical a) le_sup_right
    (sup_le hUQ inf_le_left)).symm.trans (by rw [hiUD])

/-- A critical root must move strictly more cosets in Q/D than Q/UD has.
This is the four-root contradiction used in MS93 (3.7)(2), with the full D. -/
theorem core_critical_fixed_index_gt_natural_index
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    (U d.radical a ⊔ fixedCore d.radical a).relIndex (Q d.radical a) <
      (commutatorPreimage (Q d.radical a) (Z d.radical z)
        (fixedCore d.radical a)).relIndex (Q d.radical a) := by
  let q := 2^n
  let r := (U d.radical a ⊔ fixedCore d.radical a).relIndex (Q d.radical a)
  let k := (commutatorPreimage (Q d.radical a) (Z d.radical z)
    (fixedCore d.radical a)).relIndex (Q d.radical a)
  have hq : 1 < q := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hr : r ≤ q := core_relIndex_natural_sup_fixed_le h d g hb path.start_color
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hrpos : 0 < r := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hh : q^4*r ≤ k^4 := by
    rw [←core_fixed_index_eq_natural_mul h d g hb path.start_color]
    exact core_fixed_index_le_critical_index_pow_four h d path hb hcritical
  by_contra! hkr
  have hle : q^4*r ≤ q^3*r := calc
    _ ≤ k^4 := hh
    _ ≤ r^4 := Nat.pow_le_pow_left hkr 4
    _ = r^3*r := pow_succ r 3
    _ ≤ q^3*r := Nat.mul_le_mul_right r (Nat.pow_le_pow_left hr 3)
  have he := Nat.le_of_mul_le_mul_right hle hrpos
  exact (not_le_of_gt ((pow_lt_pow_iff_right₀ hq).mpr (by decide : 3 < 4))) he
/-- The fixed-space comparison in the nonquadratic fixed-core branch,
with the complete fixed subgroup retained in the denominator. -/
theorem fixedCore_large_centralizer_comparison
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (himage : (Q d.radical z).relIndex (U d.radical a) = 2^n)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hlarge : (2^n)^2 <
      (centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    componentRadical d a t ⊓ (U d.radical z ⊔ fixedCore d.radical z) ≤
      U d.radical a ⊔ fixedCore d.radical z := by
  let A := fixedCore d.radical a
  let B := U d.radical a
  have hAT : A ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  have hB₀ : B ≤ componentRadical d a t :=
    (c.componentRadical_inf_core g hb path.start_color).symm.le.trans inf_le_left
  have hBT : B ≤ Q d.radical t := hB₀.trans inf_le_left
  have hAS : A ≤ stabilizer d.radical z := hAT.trans c'.edge_le
  have hBS : B ≤ stabilizer d.radical z := hBT.trans c'.edge_le
  have hz := path.end_color
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d hz
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have haction (x : stabilizer d.radical z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  let βA := γ.comp (inclusion hAS)
  let βB := γ.comp (inclusion hBS)
  let αB := (commutator (Sp E.Carrier)).subtype.comp βB
  have hk : αB.ker = (Q d.radical z).subgroupOf B := by
    have hkκ : κ.ker = (Q d.radical z).subgroupOf (stabilizer d.radical z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [αB,βB,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hi : Nat.card αB.range = 2^n := by
    rw [←index_ker,hk]
    exact himage
  have hBlarge : 1 < Nat.card αB.range := by
    rw [hi]
    exact one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hfull := (full_radical_centralizes_critical_root h d path hb c c' hcritical).2.2.2
  have htriple : ⁅⁅U d.radical z,B⁆,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    exact (hAT.trans hfull).trans (centralizer_le (commutator_mono le_rfl (U_le_Z a)))
  have hmove : ⁅B,U d.radical z⁆ ≤ U d.radical a := by
    rw [commutator_comm]
    exact (commutator_mono (U_le_Z z) hB₀).trans
      (paired_source_triples h d g hb hsat path hat hzt c c').1
  have hUzT : U d.radical z ≤ Q d.radical t :=
    (c'.componentRadical_inf_core g hb path.end_color).symm.le.trans
      (inf_le_left.trans inf_le_left)
  have hkernel (w : s.space.toSubmodule) :
      MovedSection.coverProjection s e w=0 ↔
        j (Multiplicative.ofAdd w) ∈ fixedCore d.radical z := by
    constructor
    · intro hw
      refine ⟨?_,(hker w).mp hw⟩
      exact ((U_le_Z z).trans ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
          (omegaCenter_le _))) (hjr ▸ ⟨_,rfl⟩)
    · exact fun hw => (hker w).mpr hw.2
  have hfixed := cover_large_centralizer_le (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he (U d.radical z) A B
    (U d.radical a) (fixedCore d.radical z) j hj hjr βA βB
    (fun x => haction (inclusion hAS x)) (fun x => haction (inclusion hBS x))
    (by simpa only [E.card_eq,hE] using hlarge) hBlarge htriple hmove hkernel
    (hUzT.trans c'.fixedCore_normalized)
  apply component_intersection_le_of_fixed_preimage (Q d.radical t)
    (componentRadical d a t) A (U d.radical z) (U d.radical a)
    (fixedCore d.radical z) inf_le_left hUzT (inf_le_left.trans c'.core_le_edge)
    (le_normalizer_iff_commutator_le_left.mp (hAT.trans c'.fixedCore_normalized))
    c'.fixedCore_normalized ?_ hfixed
  rw [commutator_comm]
  exact EdgeMarking.fixedCore_centralizes_componentRadical (d := d) (a := a) (t := t)

/-- The entire component-fixed subgroup has natural moving index at most q².
The contrary case gives the source centralizer index at most r, contradicting
four critical-root conjugates on the actual whole-core quotient. -/
theorem source_two_fixedCore_movement_le_square
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    (centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ (2^n)^2 := by
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  have hUzQ : U d.radical z ≤ Q d.radical z :=
    (c'.componentRadical_inf_core g hb path.end_color).symm.le.trans inf_le_right
  have hUaQ : U d.radical a ≤ Q d.radical a :=
    (c.componentRadical_inf_core g hb path.start_color).symm.le.trans inf_le_right
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (hUzQ.trans c'.core_le_edge)) (inclusion_injective _)
  by_contra! hlarge
  have hlargeQ : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z) :=
    hlarge.trans_le (relIndex_le_of_le_left (centralizer_le
      (show fixedCore d.radical a ≤ Q d.radical a from inf_le_left)) index_ne_zero_of_finite)
  obtain ⟨hT,hU,hZ,he⟩ := source_two_large_movement_images h d g hb hsat path hat hzt c c' hlargeQ
  have hfactor := source_two_large_movement_component_factorization h d g hb hsat path hat hzt c c' hlargeQ
  have hcomp := fixedCore_large_centralizer_comparison h d g hb hsat path hat hzt c c' hU hZ hlarge
  have hZaT : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1 < g.b d.radical
    omega
  have hbound := fixed_index_le_of_component_intersection (Q d.radical t)
    (componentRadical d a t) (Q d.radical a) (Q d.radical z)
    (U d.radical a) (U d.radical z) (fixedCore d.radical z) (Z d.radical a)
    (c.componentRadical_sup_core g (by omega)) hfactor hUaQ c'.core_le_edge hUzQ inf_le_left
    (c.edge_le.trans (Q_normalized d.radical a)) c'.fixedCore_normalized hZaT
    (by rw [commutator_comm]; exact Z_centralizes_Q d.radical a path.start_color)
    (hcomp.trans (sup_le_sup_right hUaQ _))
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hother := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hZ]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  exact (not_le_of_gt (core_critical_fixed_index_gt_natural_index h d rev hb hother)) hbound

/-- The fixed-core quadraticity step of MS93 (3.7)(2) on the full original
critical layer, including its central covering kernel and fixed attachment. -/
theorem source_two_fixedCore_quadratic
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    ⁅⁅Z d.radical z,fixedCore d.radical a⁆,fixedCore d.radical a⁆ = ⊥ := by
  have hAT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  have hsmall := source_two_fixedCore_movement_le_square h d g hb hsat path hat hzt c c'
  have hA : IsPGroup 2 (fixedCore d.radical a) :=
    (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color).of_injective
      (inclusion (show fixedCore d.radical a ≤ Q d.radical a from inf_le_left)) (inclusion_injective _)
  have hquad := moving_quadratic_of_small_index h d g (by omega) path.end_color
    (fixedCore d.radical a) (hAT.trans c'.edge_le) hA hsmall
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hcentral : Z d.radical t ≤ centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) := by
    have hZt : Z d.radical t = omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
    rw [hZt]
    exact fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hAT hy)
  have hUzT : U d.radical z ≤ Q d.radical t :=
    (c'.componentRadical_inf_core g hb path.end_color).symm.le.trans
      (inf_le_left.trans inf_le_left)
  have heq : ⁅Z d.radical z,fixedCore d.radical a⁆ = ⁅U d.radical z,fixedCore d.radical a⁆ := by
    apply le_antisymm ?_ (commutator_mono (U_le_Z z) le_rfl)
    rw [commutator_comm (Z d.radical z),commutator_comm (U d.radical z)]
    apply commutator_le_moving_of_inner_mod_centralizer (fixedCore d.radical a)
      (U d.radical z) (Z d.radical z) (hUzT.trans c.fixedCore_normalized)
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt]
    exact sup_le_sup_left hcentral _
  simpa only [heq] using hquad

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
