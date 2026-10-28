module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFive
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeGenerators
public import Theory.Representation.SymplecticFourOrthogonalCover.MovingIndex

/-!
# Equality of the full Z-layers in MS93 (3.7)(5)

An actor of order q modulo the entire endpoint core, with omega-layer
movement of at most q modulo the complete attachment, fixes only elements
of Z inside X. The natural submodule injects its displacement into that
whole-core quotient movement. Its displacement therefore has dimension one;
the full root preserves no quadratic refinement. The dual-cover fixed-vector
theorem puts the fixed involution in U times the complete fixed core, and its
fixed involution factor belongs to the actual midpoint omega-center.

For two neighbors satisfying the three printed antecedents of (5), the
previous core comparison identifies their full cores and X-layers. In the
large critical-image branch the Q₂ element-centralizer counts transfer across
that equality and the equal complete attachments. The fixed-vector criterion
gives containment of their Z-layers; conjugacy of neighbors gives equal order.
In the field-sized branch, source (3) already identifies X with Z.

Thus this module finishes (5), retaining the original graph, radical,
quotient/action maps, and all fixed kernels. Selection of the order-q critical
pair in (6), and the degree-two/block assembly, remain separate source steps.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(5), printed pp.875--876; the dual-cover argument is (1.5)(ii).
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo

private theorem small_displacement_no_refinement
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hE : 2 < Nat.card E) (A : Subgroup (Sp E))
    (hc : Nat.card A=Nat.card E) (hm : Nat.card (displacementSpace A) ≤ Nat.card E) :
    ¬ ∃ c : Vector E, ∀ a : A, ∀ v,
      Plane.OrthogonalActors.refinement c (a.val • v)=Plane.OrthogonalActors.refinement c v := by
  let D := displacementSpace A
  have hd : Module.finrank E D ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := E)] at hm
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card E)).mp (by simpa using hm)
  have hn : D≠⊥ := by
    intro hz
    have hAb : A=⊥ := by
      apply bot_unique
      intro a ha
      apply Subtype.ext
      ext i j
      have hh := Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp A.subtype)
        ⟨a,ha⟩ (Pi.single j 1)
      change a • Pi.single j 1-Pi.single j 1 ∈ D at hh
      rw [hz] at hh
      have he := congrFun (sub_eq_zero.mp hh) i
      simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec_single,
        Matrix.one_apply,Pi.single_apply] using he
    rw [hAb,Subgroup.card_bot] at hc
    omega
  have hd1 : Module.finrank E D=1 := by
    have hp : Module.finrank E D≠0 := fun he => hn (Submodule.finrank_eq_zero.mp he)
    omega
  have hiso : D ≤ (form E).orthogonal D := by
    obtain ⟨v,hv,hv0⟩ := D.ne_bot_iff.mp hn
    have hs := eq_span_singleton_of_mem_of_finrank_eq_one hd1 hv hv0
    intro x hx y hy
    rw [hs] at hx hy
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [TwoLocalCover.form_alternating v]
  have hquad : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector E, x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    have hv := hiso (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp A.subtype) ⟨y,hy⟩ v)
    rw [orthogonal_displacementSpace] at hv
    exact hv x hx
  exact no_refinement_of_displacement_one hE A hc hd1 hquad

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The order-q and omega-displacement counts in source (5) force every
fixed involution into the actual generated Z-layer. -/
theorem source_five_fixed_omega_mem_Z
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (c : EdgeMarking h d a t)
    (B : Subgroup (FreeAmalgam d.radical)) (hBT : B ≤ Q d.radical t)
    (hcard : (Q d.radical a).relIndex B=2^n)
    (hmove : (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅X d.radical a,B⁆ ≤ 2^n)
    (x : FreeAmalgam d.radical) (hx : x ∈ X d.radical a)
    (hfix : x ∈ centralizer (B : Set (FreeAmalgam d.radical))) :
    x ∈ Z d.radical a := by
  obtain ⟨E,hE,s,γ,hγ,i,hi,hd,hrange,_⟩ := wholeKernel_natural_dualCover h d g hb ha
  have hCtop : replacementComponent d=⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hγonto : Function.Surjective γ := MonoidHom.range_eq_top.mp (hγ.trans hCtop)
  have hγinj : Function.Injective γ := by
    intro a b hab
    apply binaryNatural_injective
    apply LinearMap.ext
    intro v
    apply hi
    rw [i.isIntertwining,i.isIntertwining]
    change s.action (γ a) (i v)=s.action (γ b) (i v)
    rw [hab]
  let e := MulEquiv.ofBijective γ ⟨hγinj,hγonto⟩
  have hBS := hBT.trans c.edge_le
  let β := e.symm.toMonoidHom.comp (s.quotient.comp (inclusion hBS))
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hβ (b : B) : γ (β b)=s.quotient (inclusion hBS b) := e.apply_symm_apply _
  have hk : α.ker=(Q d.radical a).subgroupOf B := by
    dsimp only [α,β]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.ker_comp_of_injective _ _ e.symm.injective,←MonoidHom.comap_ker]
    have hs : s.quotient.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
      rw [←s.quotient_kernel,subgroupOf_map_subtype_eq]
    rw [hs,comap_inclusion_subgroupOf]
  have hEc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) hE)
  have hc : Nat.card α.range=Nat.card E.Carrier := by
    rw [←index_ker,hk,hEc]
    exact hcard
  let π := s.sectionData.coordinates
  let N := ⁅X d.radical a,B⁆
  have hXQ : X d.radical a ≤ Q d.radical a := omegaCenter_le _
  have hUX : U d.radical a ≤ X d.radical a := (U_le_Z a).trans
    (g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0<g.b d.radical; omega))
  have hNQ : N ≤ Q d.radical a := by
    dsimp only [N]
    rw [commutator_comm]
    exact (commutator_mono le_rfl hXQ).trans
      (le_normalizer_iff_commutator_le_right.mp (hBS.trans (Q_normalized d.radical a)))
  let N₀ := (N.subgroupOf (Q d.radical a)).map π
  have hNc : Nat.card N₀ ≤ Nat.card E.Carrier := by
    have he : Nat.card N₀=(fixedCore d.radical a).relIndex N := by
      rw [←relIndex_ker,s.sectionData.kernel_eq,relIndex_subgroupOf hNQ]
      rfl
    rw [he,hEc]
    apply le_trans ?_ hmove
    let := finite_stabilizer d.radical a
    let : Finite N := Finite.of_injective
      (inclusion (hNQ.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)))
      (inclusion_injective _)
    apply relIndex_le_of_le_left ?_ index_ne_zero_of_finite
    exact inf_le_inf (hUX.trans hXQ) le_rfl
  have hgen (b : B) (v : Vector E.Carrier) :
      Multiplicative.ofAdd (i (α b • v-v)) ∈ N₀ := by
    obtain ⟨u,hu,heu⟩ := (hrange (i v)).mp ⟨v,rfl⟩
    let w : Q d.radical a :=
      ⟨b.val*u.val*b.val⁻¹,
        (mem_normalizer_iff.mp (Q_normalized d.radical a (hBS b.property)) u).mp u.property⟩*u⁻¹
    refine ⟨w,?_,?_⟩
    · change ⁅b.val,u.val⁆ ∈ ⁅X d.radical a,B⁆
      rw [commutator_comm]
      exact commutator_mem_commutator b.property (hUX hu)
    · apply Multiplicative.toAdd.injective
      change (π w).toAdd=i (α b • v-v)
      dsimp only [w,π]
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg]
      have heq := s.sectionData.equivariant (inclusion hBS b) u
      change (s.sectionData.coordinates ⟨b.val*u.val*b.val⁻¹,_⟩).toAdd=
        s.action (s.quotient (inclusion hBS b)) (s.sectionData.coordinates u).toAdd at heq
      rw [heq,heu,map_sub]
      change s.action (s.quotient (inclusion hBS b)) (i v)-i v=
        i (binaryNatural (β b) v)-i v
      rw [i.isIntertwining]
      change s.action (s.quotient (inclusion hBS b)) (i v)-i v=
        s.action (γ (β b)) (i v)-i v
      rw [hβ]
  have hD (v : Vector E.Carrier) (hv : v ∈ displacementSpace α.range) :
      Multiplicative.ofAdd (i v) ∈ N₀ := by
    have hs : ∀ k : E.Carrier, Multiplicative.ofAdd (i (k • v)) ∈ N₀ := by
      induction hv using Submodule.span_induction with
      | mem v hv =>
        rcases hv with ⟨⟨b,w⟩,rfl⟩
        obtain ⟨a,ha⟩ := b.property
        intro k
        change Multiplicative.ofAdd (i (k • (b.val • w-w))) ∈ N₀
        rw [←ha]
        simpa only [smul_sub,smul_comm (α a) k] using hgen a (k • w)
      | zero => intro k; simp
      | add v w hv hw ihv ihw =>
        intro k
        simpa only [smul_add,map_add,ofAdd_add] using N₀.mul_mem (ihv k) (ihw k)
      | smul k v hv ih => intro l; simpa only [smul_smul] using ih (l*k)
    simpa only [one_smul] using hs 1
  have hDc : Nat.card (displacementSpace α.range) ≤ Nat.card E.Carrier := by
    let f : displacementSpace α.range → N₀ := fun v => ⟨Multiplicative.ofAdd (i v),hD v v.property⟩
    have hf : Function.Injective f := by
      intro v w he
      exact Subtype.ext (hi (Multiplicative.ofAdd.injective (congrArg Subtype.val he)))
    exact (Nat.card_le_card_of_injective f hf).trans hNc
  have hElarge : 2<Nat.card E.Carrier := by
    rw [hEc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  have hno := small_displacement_no_refinement hElarge α.range hc hDc
  have hno' : ¬ ∃ v : Natural (K := E.Carrier), ∀ b : β.range, ∀ w,
      Plane.OrthogonalActors.refinement v (binaryNatural b.val w)=Plane.OrthogonalActors.refinement v w := by
    rintro ⟨v,hv⟩
    apply hno
    refine ⟨v,?_⟩
    rintro ⟨b,⟨y,rfl⟩⟩ w
    exact hv ⟨β y,⟨y,rfl⟩⟩ w
  let xQ : Q d.radical a := ⟨x,hXQ hx⟩
  have hfixed : (π xQ).toAdd ∈ OneCohomology.fixed ((s.action.comp γ).comp β.range.subtype) := by
    rintro ⟨b,⟨y,rfl⟩⟩
    change s.action (γ (β y)) (π xQ).toAdd=_
    rw [hβ]
    have heq := s.sectionData.equivariant (inclusion hBS y) xQ
    change (π ⟨y.val*x*y.val⁻¹,_⟩).toAdd=
      s.action (s.quotient (inclusion hBS y)) (π xQ).toAdd at heq
    rw [←heq]
    congr 2
    apply Subtype.ext
    change y.val*x*y.val⁻¹=x
    rw [hfix y.val y.property,mul_inv_cancel_right]
  have hmem := dualCover_fixed_le_natural_of_no_refinement i hi hd β.range hno' hfixed
  obtain ⟨u,hu,heu⟩ := (hrange _).mp hmem
  have hdu : (u⁻¹*xQ : Q d.radical a) ∈ π.ker := by
    change π (u⁻¹*xQ)=1
    rw [map_mul,map_inv,Multiplicative.toAdd.injective heu,inv_mul_cancel]
  rw [s.sectionData.kernel_eq] at hdu
  have hdX : u.val⁻¹*x ∈ X d.radical a :=
    (X d.radical a).mul_mem ((X d.radical a).inv_mem (hUX hu)) hx
  have hdZ := replacement_fixed_X_le_edge h d (g := g) (by omega) ha hat ⟨hdX,hdu.2⟩
  have hh := (Z d.radical a).mul_mem (U_le_Z a hu)
    (Sp4Four.edge_Z_le_endpoint d.radical ha hat hdZ)
  simpa only [mul_inv_cancel_left] using hh


/-- MS93 (3.7)(5), with the same midpoint and all three printed antecedents.
The centralizer count handles the plane branch; source (3) handles the
field-sized branch. -/
theorem source_five_Z_equality
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t v : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hvt : Adjacent d.radical v t) (hv : color d.radical v=false)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) (cv : EdgeMarking h d v t)
    (hfixed : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical v ⊓ centralizer (Ltilde d.radical v : Set (FreeAmalgam d.radical)))
    (hmove : ⁅Z d.radical v,Q d.radical t⁆=⁅Z d.radical a,Q d.radical t⁆)
    (hinside : Z d.radical v ≤ Q d.radical a) :
    Z d.radical v=Z d.radical a := by
  obtain ⟨hQ,hX⟩ := source_five_core_equality h d g hb path.start_color hv c cv hfixed hmove hinside
  have hcard : Nat.card (Z d.radical a)=Nat.card (Z d.radical v) := by
    obtain ⟨u,_,he⟩ := stabilizer_transitive_neighbors d.radical t
      (adjacent_symm d.radical hat) (adjacent_symm d.radical hvt)
    rw [←he,Z_act,card_map_of_injective (MulAut.conj u⁻¹).injective]
  let := finite_Z d.radical a
  let := finite_Z d.radical v
  by_cases hlarge : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)
  · apply (Subgroup.eq_of_le_of_card_ge (K := Z d.radical v) ?_ hcard.ge).symm
    intro x hx
    by_cases hxt : x ∈ Z d.radical t
    · exact Sp4Four.edge_Z_le_endpoint d.radical hv hvt hxt
    have hc := source_five_large_omega_displacement h d g hb hsat path hat hzt c c' hlarge x hx hxt
    let B := Q d.radical t ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    apply source_five_fixed_omega_mem_Z h d g hb hv hvt cv B inf_le_left
      (by rw [←hQ]; exact hc.1) (by rw [←hfixed,←hX]; exact hc.2.le) x
      (hX ▸ g.omega_bound a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega) hx)
    intro b hb
    exact mem_centralizer_singleton_iff.mp hb.2
  · have hsmall := (replacement_critical_indices_eq_field_of_small h d path (by omega)
      (lt_of_not_ge hlarge)).1
    have he := (source_three_of_field_critical h d g hb hsat path hat hzt c c' hsmall).2.2.1
    apply Subgroup.eq_of_le_of_card_ge ?_ hcard.le
    rw [←he,hX]
    exact g.omega_bound v hv (by rw [g.distance_constant v hv]; change 0<g.b d.radical; omega)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
