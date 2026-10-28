module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalKernelComparison
public import Theory.GroupTheory.NormalSectionTwoResidual

/-!
# Full critical commutators on unequal terminal paths

The actual unequal-mover terminal sequence has two-periodic full moving
central kernels. Its mutual critical-kernel commutator has exactly field
order, lies in the preceding full critical commutator, and retains the
entire joined first-edge intersection. The retained kernel propagates
through all subsequent selected vertex centers.

A nonzero fixed-subspace commutator has at least field order even after
quotienting by the entire fixed kernel: scalar multiples of one moved
vector give distinct projected commutators. Applying this to the literal
replacement cover proves that the mutual kernel commutator, together with
the whole endpoint fixed kernel, generates the preceding full critical
commutator. At distance six, kernel periodicity places that commutator in
the next selected starting seed. The intersection of the two starting
seeds is then invariant under the selected individual mover and endpoint.
The simple quotient forces it to contain the full original moving layer.
Its fixed index would be at most q squared, contradicting the unequal
neighbor's larger index. Thus the unequal-mover distance-six case is
excluded on the same sequence, retaining original mover fixedness,
normalizer escape, reciprocal indices and all Z/X/U identities.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), proof of (5.10), printed pp.922--923. The opposite normalizer
comparison, unequal-mover exclusion, (5.11)--(5.12) and the actual minimum
characteristic-replacement distance-two witness remain necessary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
private theorem central_seed_le_incident_edge
    {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}
    (hb : 2 < geometry.b R) {a c t : Vertex R}
    (ha : color R a=false) (hat : Adjacent R a t) (hct : Adjacent R c t) :
    Z R a ⊓ centralizer (stabilizer R c : Set (FreeAmalgam R)) ≤ Z R t := by
  have ht : color R t ≠ false := fun ht => (adjacent_color_ne R hat) (ha.trans ht.symm)
  have hZT : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha,
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)]
    exact lt_trans (by decide : 1 < 2) hb
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary (by omega) a ha
  rintro x ⟨hx,hc⟩
  rw [Z,if_neg ht]
  apply mem_omegaCenter_iff.mpr
  refine ⟨hZT hx,elemPow_eq_one_of_isElementaryAbelian _ hx,?_⟩
  exact (centralizer_le (show Q R t ≤ stabilizer R c from
    fun _ hy => hy.2 c (adjacent_symm R hct))) hc

private theorem full_center_transport
    {M : Type*} [Group M] {R : Subgroup M}
    (A : Subgroup (FreeAmalgam R)) {a c v : Vertex R}
    (ha : A ≤ stabilizer R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)))
    (hc : A ≤ centralizer (stabilizer R c : Set (FreeAmalgam R)))
    {y : FreeAmalgam R} (hy : y ∈ stabilizer R c) (hv : act R y a=v) :
    A ≤ stabilizer R v ⊓ centralizer (stabilizer R v : Set (FreeAmalgam R)) := by
  have hfixed : A.map (MulAut.conj y⁻¹).toMonoidHom=A :=
    mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hc ((stabilizer R c).inv_mem hy)))
  have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) ha
  rw [hfixed,map_inf _ _ _ (MulAut.conj y⁻¹).injective,
    Theory.GroupTheory.map_centralizer_equiv] at hh
  change A ≤ (stabilizer R a).map (MulAut.conj y⁻¹).toMonoidHom ⊓
    centralizer (((stabilizer R a).map (MulAut.conj y⁻¹).toMonoidHom : Subgroup (FreeAmalgam R)) : Set _) at hh
  rw [←stabilizer_act,hv] at hh
  exact hh

/-- Residual two-step orbit shifts propagate a retained full-center subgroup
through all the subsequent chosen starting vertices. -/
private theorem unequal_path_full_center_propagation
    {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}
    (hb : 2 ≤ geometry.b R) (q : ℕ)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (unequalPathChoice geometry q) (s i) (s (i+1)))
    (A : Subgroup (FreeAmalgam R)) (i : ℕ)
    (h₀ : A ≤ stabilizer R (s i).first ⊓
      centralizer (stabilizer R (s i).first : Set (FreeAmalgam R)))
    (h₁ : A ≤ stabilizer R (s (i+1)).first ⊓
      centralizer (stabilizer R (s (i+1)).first : Set (FreeAmalgam R))) :
    ∀ k, A ≤ stabilizer R (s (i+k)).first ⊓
      centralizer (stabilizer R (s (i+k)).first : Set (FreeAmalgam R)) := by
  have hpair : ∀ k,
      (A ≤ stabilizer R (s (i+k)).first ⊓
        centralizer (stabilizer R (s (i+k)).first : Set (FreeAmalgam R))) ∧
      (A ≤ stabilizer R (s (i+k+1)).first ⊓
        centralizer (stabilizer R (s (i+k+1)).first : Set (FreeAmalgam R))) := by
    intro k
    induction k with
    | zero => simpa only [Nat.add_zero] using And.intro h₀ h₁
    | succ k ih =>
      refine ⟨by simpa only [Nat.add_assoc] using ih.2,?_⟩
      obtain ⟨t,⟨⟨y,hy,hyv,hyt,hidx⟩,hgen,hfix,hres⟩,hct,hat,hfirst⟩ := (hs (i+k+1)).choice
      have he := (hs (i+k)).overlap 0 hb
      simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
      rw [he] at hyv
      have hh := full_center_transport A ih.1 (ih.2.trans inf_le_right)
        (Ltilde_le_stabilizer _ hy) hyv.symm
      simpa only [Nat.add_assoc] using hh
  exact fun k => (hpair k).1

private theorem moving_center_kernel_act
    {M : Type*} [Group M] {R : Subgroup M} (y : FreeAmalgam R) (a : Vertex R) :
    U R (act R y a) ⊓ centralizer (stabilizer R (act R y a) : Set (FreeAmalgam R)) =
      (U R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R))).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,stabilizer_act,map_inf _ _ _ (MulAut.conj y⁻¹).injective,
    Theory.GroupTheory.map_centralizer_equiv]
  simp only [coe_map,MulEquiv.coe_toMonoidHom]

private theorem fixed_index_of_split {G : Type*} [Group G]
    (X U C E : Subgroup G) [IsMulCommutative X]
    (hUX : U ≤ X) (hsplit : X = U ⊔ C)
    (hCE : C ≤ centralizer (E : Set G)) :
    (centralizer (E : Set G)).relIndex X =
      (centralizer (E : Set G)).relIndex U := by
  let Y := X ⊓ centralizer (E : Set G)
  have hCX : C ≤ X := le_sup_right.trans_eq hsplit.symm
  have hjoin : U ⊔ Y = X := by
    apply le_antisymm (sup_le hUX inf_le_left)
    exact hsplit.le.trans (sup_le le_sup_left
      ((show C ≤ Y from le_inf hCX hCE).trans le_sup_right))
  let : CommGroup X := IsMulCommutative.instCommGroup
  have hh := relIndex_sup_right (U.subgroupOf X) (Y.subgroupOf X)
  rw [←subgroupOf_sup hUX (show Y ≤ X from inf_le_left),hjoin,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf hUX] at hh
  have he (V : Subgroup G) (hv : V ≤ X) :
      Y.subgroupOf V = (centralizer (E : Set G)).subgroupOf V := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hv x.property,hx⟩⟩
  change (Y.subgroupOf X).index = (Y.subgroupOf U).index at hh
  rwa [he X le_rfl,he U hUX] at hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem unequal_terminal_saturation
    {geometry : Geometry d.radical} (hb : 4 < geometry.b d.radical)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (unequalPathChoice geometry (Nat.card F)) (s i) (s (i+1)))
    (i : ℕ) :
    let C := fun j => U d.radical (s j).first ⊓
      centralizer (stabilizer d.radical (s j).first : Set (FreeAmalgam d.radical))
    let D := ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆
    C (i+2)=C i ∧
    D ⊓ Z d.radical ((s (i+2)).path.walk.getVert 1)=C (i+2) ∧
    (∀ k, C (i+2) ≤ stabilizer d.radical (s (i+k)).first ⊓
      centralizer (stabilizer d.radical (s (i+k)).first : Set (FreeAmalgam d.radical))) := by
  dsimp only
  have hcent : ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆ ⊓
      Z d.radical ((s (i+2)).path.walk.getVert 1) ≤
      (stabilizer d.radical (s (i+1)).first ⊓
        centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) ⊓
      (stabilizer d.radical (s i).first ⊓
        centralizer (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical))) ⊓
      (stabilizer d.radical (s (i+2)).first ⊓
        centralizer (stabilizer d.radical (s (i+2)).first : Set (FreeAmalgam d.radical))) := by
    obtain ⟨v,hv,hav,hcv,hfirst₁⟩ := (hs i).choice
    obtain ⟨t,ht,hct,hat,hfirst₂⟩ := (hs (i+1)).choice
    obtain ⟨y,hy,hyv,hyt,hidx⟩ := ht.1
    have he := (hs i).overlap 0 (by omega)
    simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
    rw [he] at hyv
    have htcol : color d.radical t=true := by
      have hn := adjacent_color_ne d.radical hct
      rw [(s (i+1)).path.start_color] at hn
      cases hh : color d.radical t <;> simp_all
    rw [show i+2=i+1+1 by omega,hfirst₂]
    exact fourth_shift_intersection_le_full_centers hb (unequalPathChoice geometry (Nat.card F))
      (fun j => s (i+j)) (fun j => by simpa only [Nat.add_assoc] using hs (i+j))
      hct hcv htcol ht.2.1.ge hv.2.1.ge y (Ltilde_le_stabilizer _ hy) hyv.symm
  let a := (s (i+2)).first
  let z := (s (i+2)).last
  let t := (s (i+2)).path.walk.getVert 1
  let D := ⁅Z d.radical a,Z d.radical z⁆
  let C := stabilizer d.radical a ⊓
    centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      ((s (i+2)).path.walk.adj_getVert_succ
        (by rw [(s (i+2)).path.length_eq_b]; omega : 0 < (s (i+2)).path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hD : D ≤ Z d.radical a := critical_commutator_le_start (s (i+2)) (by omega)
  have heq : D ⊓ Z d.radical t = D ⊓ C := by
    apply le_antisymm
    · exact le_inf inf_le_left (hcent.trans inf_le_right)
    · exact le_inf inf_le_left
        ((le_inf (inf_le_left.trans hD) (inf_le_right.trans inf_le_right)).trans
          (central_seed_le_incident_edge (geometry := geometry) (by omega) (s (i+2)).path.start_color hat hat))
  have hall : ∀ k, D ⊓ C ≤ stabilizer d.radical (s (i+k)).first ⊓
      centralizer (stabilizer d.radical (s (i+k)).first : Set (FreeAmalgam d.radical)) := by
    apply unequal_path_full_center_propagation (by omega) (Nat.card F) s hs (D ⊓ C) i
    · rw [←heq]
      exact hcent.trans (inf_le_left.trans inf_le_right)
    · rw [←heq]
      exact hcent.trans (inf_le_left.trans inf_le_left)
  have hsat := h.replacement_critical_commutator_full_center_kernel d (s (i+2)).path hb.le
  change D ⊓ C = _ at hsat
  rw [hsat] at heq hall
  let C' := fun j => U d.radical (s j).first ⊓
    centralizer (stabilizer d.radical (s j).first : Set (FreeAmalgam d.radical))
  have hperiod : C' (i+2)=C' i := by
    obtain ⟨t,⟨⟨y,hy,hyv,hyt,hidx⟩,hgen,hfix,hres⟩,hct,hat,hfirst⟩ := (hs (i+1)).choice
    have he := (hs i).overlap 0 (by omega)
    simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
    rw [he] at hyv
    have hc : C' (i+2) ≤ centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical)) :=
      (hall 1).trans inf_le_right
    have hfixed : (C' (i+2)).map (MulAut.conj y⁻¹).toMonoidHom=C' (i+2) :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hc ((stabilizer d.radical (s (i+1)).first).inv_mem
          (Ltilde_le_stabilizer _ hy))))
    have htransport := moving_center_kernel_act y (s i).first
    rw [←hyv] at htransport
    have heqmap : (C' (i+2)).map (MulAut.conj y⁻¹).toMonoidHom =
        (C' i).map (MulAut.conj y⁻¹).toMonoidHom := hfixed.trans htransport
    exact map_injective (MulAut.conj y⁻¹).injective heqmap
  exact ⟨hperiod,heq,hall⟩



open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover

omit h d in
private theorem embedded_subspace_commutator_central_index_ge_field
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y A C : Subgroup G) (D : Submodule F (Vector F)) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hA : ∀ w : W, j (Multiplicative.ofAdd w) ∈ A ↔ p w ∈ D)
    (hAr : A ≤ j.range) (hn : ⁅Y,A⁆ ≠ ⊥)
    (hker : ∀ w : W, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ C) :
    Nat.card F ≤ C.relIndex ⁅Y,A⁆ := by
  classical
  have hdisp (y : Y) (w : W) :
      j (Multiplicative.ofAdd (σ (β y) w-w))=⁅y.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  obtain ⟨π,hπ⟩ := exists_embedded_projection j.range j hj rfl p.toLinearMap
  have hk : π.ker=C.subgroupOf j.range := by
    ext u
    obtain ⟨w,hw⟩ := u.property
    have he : u=⟨j w,⟨w,rfl⟩⟩ := Subtype.ext hw.symm
    subst u
    change π ⟨j w,_⟩=1 ↔ j w ∈ C
    have hπw := hπ w.toAdd
    change π ⟨j w,_⟩=Multiplicative.ofAdd (p w.toAdd) at hπw
    rw [hπw]
    exact hker w.toAdd
  have hbound : ⁅Y,A⁆ ≤ j.range := by
    apply commutator_le.mpr
    intro y hy a ha
    obtain ⟨w,rfl⟩ := hAr ha
    change ⁅(⟨y,hy⟩ : Y).val,j (Multiplicative.ofAdd w.toAdd)⁆ ∈ j.range
    rw [←hdisp]
    exact ⟨_,rfl⟩
  have hex : ∃ y ∈ Y, ∃ a ∈ A, ⁅y,a⁆ ≠ 1 := by
    by_contra! hh
    apply hn
    exact le_bot_iff.mp (commutator_le.mpr fun y hy a ha => mem_bot.mpr (hh y hy a ha))
  obtain ⟨y,hy,a,ha,hne⟩ := hex
  obtain ⟨w,rfl⟩ := hAr ha
  let δ := symplecticNatural (k := F) 2 (β ⟨y,hy⟩).val (p w.toAdd)-p w.toAdd
  have hd : δ ≠ 0 := by
    intro hd
    have hf := cover_fixed_of_projection_fixed p hp (β ⟨y,hy⟩) w.toAdd (sub_eq_zero.mp hd)
    apply hne
    change ⁅(⟨y,hy⟩ : Y).val,j (Multiplicative.ofAdd w.toAdd)⁆=1
    rw [←hdisp,hf,sub_self,ofAdd_zero,map_one]
  have hchoose (t : F) : ∃ u : W, p u=t • p w.toAdd := hp.1 _
  choose u hu using hchoose
  have hmem (t : F) : j (Multiplicative.ofAdd (u t)) ∈ A :=
    (hA _).mpr (hu t ▸ D.smul_mem t ((hA _).mp ha))
  let f : F → ((⁅Y,A⁆.subgroupOf j.range).map π) := fun t =>
    ⟨π ⟨⁅y,j (Multiplicative.ofAdd (u t))⁆,hbound (commutator_mem_commutator hy (hmem t))⟩,
      ⟨_,commutator_mem_commutator hy (hmem t),rfl⟩⟩
  have hf : Function.Injective f := by
    intro t s he
    have hfval (r : F) : (f r).val=Multiplicative.ofAdd (r • δ) := by
      change π ⟨⁅y,j (Multiplicative.ofAdd (u r))⁆,_⟩=_
      have hv : (⟨⁅y,j (Multiplicative.ofAdd (u r))⁆,hbound (commutator_mem_commutator hy (hmem r))⟩ : j.range)=
          ⟨j (Multiplicative.ofAdd (σ (β ⟨y,hy⟩) (u r)-u r)),⟨_,rfl⟩⟩ :=
        Subtype.ext (hdisp ⟨y,hy⟩ (u r)).symm
      rw [hv,hπ]
      congr 1
      change p (σ (β ⟨y,hy⟩) (u r)-u r)=_
      rw [map_sub,p.isIntertwining,hu r]
      change symplecticNatural 2 (β ⟨y,hy⟩).val (r • p w.toAdd)-r • p w.toAdd=_
      rw [map_smul,←smul_sub]
    have hv := congrArg Subtype.val he
    rw [hfval,hfval] at hv
    exact (smul_left_injective F hd) (Multiplicative.ofAdd.injective hv)
  rw [←relIndex_subgroupOf hbound,←hk,relIndex_ker]
  exact Nat.card_le_card_of_injective f hf

omit h d in
private theorem embedded_fixed_subspace_commutator_central_index_ge_field
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T C : Subgroup G) (β : Y →* L (K := F)) (γ : T →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hactT : ∀ (t : T) (w : W), j (Multiplicative.ofAdd (σ (γ t) w)) =
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (hn : ⁅Y,j.range ⊓ centralizer (T : Set G)⁆ ≠ ⊥)
    (hker : ∀ w : W, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ C) :
    Nat.card F ≤ C.relIndex ⁅Y,j.range ⊓ centralizer (T : Set G)⁆ := by
  let α := (commutator (Sp F)).subtype.comp γ
  apply embedded_subspace_commutator_central_index_ge_field p hp j hj Y
    (j.range ⊓ centralizer (T : Set G)) C (TwoLocalCover.fixedSpace α.range) β hact
    ?_ inf_le_left hn hker
  intro w
  constructor
  · intro hw t ht
    obtain ⟨t,rfl⟩ := ht
    have he : σ (γ t) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hactT,hw.2 t.val t.property,mul_inv_cancel_right]
    exact (LinearMap.congr_fun (p.isIntertwining' (γ t)) w).symm.trans (congrArg p he)
  · intro hw
    refine ⟨⟨_,rfl⟩,fun t ht => ?_⟩
    have hf := cover_fixed_of_projection_fixed p hp (γ ⟨t,ht⟩) w
      (hw (α ⟨t,ht⟩) ⟨_,rfl⟩)
    have he := congrArg (fun w => j (Multiplicative.ofAdd w)) hf
    rw [hactT,mul_inv_eq_iff_eq_mul] at he
    exact he

private theorem fixed_intersection_commutator_central_index_ge_field
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z=false)
    (Y T : Subgroup (FreeAmalgam d.radical))
    (hYS : Y ≤ stabilizer d.radical z) (hTS : T ≤ stabilizer d.radical z)
    (hn : ⁅Y,U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ ≠ ⊥) :
    Nat.card F ≤ (centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
      ⁅Y,U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d hz
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : stabilizer d.radical z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (γ y) w))=y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC y))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj y w
  have hh := embedded_fixed_subspace_commutator_central_index_ge_field p he j hj Y T
    (centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (γ.comp (inclusion hYS)) (γ.comp (inclusion hTS))
    (fun y w => hact (inclusion hYS y) w) (fun t w => hact (inclusion hTS t) w)
    (by rwa [hjr]) hker
  rwa [hFc,hjr] at hh

/-- The nonzero full critical-intersection commutator has at least q
images modulo the entire endpoint fixed subgroup. -/
theorem Input.replacement_root_intersection_central_index_ge_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYS : Y ≤ stabilizer d.radical z)
    (hn : ⁅Y,X d.radical z ⊓ Q d.radical a⁆ ≠ ⊥) :
    Nat.card F ≤ (centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
      ⁅Y,X d.radical z ⊓ Q d.radical a⁆ := by
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hAU : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have heq := (h.replacement_root_intersection_fixed_and_commutator d path hb hsmall Y hYS).1
  rw [←hAU] at heq
  rw [heq] at hn ⊢
  exact fixed_intersection_commutator_central_index_ge_field h d geometry hb path.end_color
    Y (Z d.radical a) hYS
    (Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le) hn


omit h d in
private theorem join_eq_of_equal_relative_index {G : Type*} [Group G]
    (C D W : Subgroup G) [IsMulCommutative W] [Finite W]
    (hCW : C ≤ W) (hDW : D ≤ W) (hi : C.relIndex D=C.relIndex W) :
    D ⊔ C=W := by
  let : CommGroup W := IsMulCommutative.instCommGroup
  have hJ : D ⊔ C ≤ W := sup_le hDW hCW
  have hidx : C.relIndex (D ⊔ C)=C.relIndex D := by
    have hh := relIndex_sup_right (D.subgroupOf W) (C.subgroupOf W)
    rw [←subgroupOf_sup hDW hCW,relIndex_subgroupOf hJ,relIndex_subgroupOf hDW] at hh
    exact hh
  have hm := relIndex_mul_relIndex C (D ⊔ C) W le_sup_right hJ
  rw [hidx,hi] at hm
  have hone : (D ⊔ C).relIndex W=1 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0<C.relIndex W from Nat.pos_of_ne_zero index_ne_zero_of_finite)
    simpa only [mul_one] using hm
  exact le_antisymm hJ (relIndex_eq_one.mp hone)

/-- When a critical intersection has exactly field order, it and the
entire fixed kernel generate the preceding full critical commutator. -/
theorem Input.replacement_critical_commutator_eq_intersection_join_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hi : (Q d.radical a).relIndex (Z d.radical z)=Nat.card F)
    (hi' : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYS : Y ≤ stabilizer d.radical z)
    (hn : ⁅Y,X d.radical z ⊓ Q d.radical a⁆ ≠ ⊥)
    (hbound : ⁅Y,X d.radical z ⊓ Q d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆)
    (hcard : Nat.card (⁅Y,X d.radical z ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card F) :
    ⁅Z d.radical a,Z d.radical z⁆ = ⁅Y,X d.radical z ⊓ Q d.radical a⁆ ⊔
      (U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  let D := ⁅Y,X d.radical z ⊓ Q d.radical a⁆
  let W := ⁅Z d.radical a,Z d.radical z⁆
  let C := U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  let hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge (by omega)
  have hWZ : W ≤ Z d.radical z := critical_commutator_le_endpoint ⟨a,z,path⟩
  have hWU : W ≤ U d.radical z := by
    change ⁅Z d.radical a,Z d.radical z⁆ ≤ U d.radical z
    rw [commutator_comm (Z d.radical a)]
    rw [h.replacement_Z_commutator_eq_U d geometry hb path.end_color
      (Z d.radical a) (Z_le_stabilizer_of_dist_le a
        (geometry.exists_critical a path.start_color) path.critical.1.le)]
    exact le_normalizer_iff_commutator_le_left.mp
      ((Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color)
        path.critical.1.le).trans (U_normalized z))
  have hCW : C ≤ W := (inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer z))).trans
    (le_sup_right.trans (h.replacement_critical_commutator_contains_fixed_kernels d path (by omega)))
  let : IsElementaryAbelian 2 (Z d.radical z) := geometry.Z_elementary (by omega) z path.end_color
  let : IsMulCommutative W := ⟨⟨fun x y => Subtype.ext
    (setLike_mul_comm (hWZ x.property) (hWZ y.property))⟩⟩
  let := finite_Z d.radical z
  let : Finite W := Finite.of_injective (inclusion hWZ) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hbound) (inclusion_injective _)
  have hsmall : (Q d.radical z).relIndex (Z d.radical a)<Nat.card F^2 := by
    rw [hi']; have hq : 1<Nat.card F := Finite.one_lt_card; nlinarith
  have hlo := h.replacement_root_intersection_central_index_ge_field d path hb hsmall Y hYS hn
  have hloC : Nat.card F ≤ C.relIndex D := hlo.trans
    (relIndex_le_of_le_left (inf_le_right.trans (centralizer_le (Ltilde_le_stabilizer z)))
      index_ne_zero_of_finite)
  have hDC : C.relIndex D=Nat.card F := le_antisymm
    (by rw [←hcard]; exact Nat.le_of_dvd (Nat.card_pos (α := D)) (relIndex_dvd_card C D)) hloC
  have hWC : C.relIndex W=Nat.card F := by
    have hidx := h.replacement_critical_commutator_central_index d rev.path hb
    change (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))).relIndex
      ⁅Z d.radical z,Z d.radical a⁆ = (Q d.radical a).relIndex (Z d.radical z) at hidx
    rw [commutator_comm,hi] at hidx
    have heq : W ⊓ C=W ⊓ (stabilizer d.radical z ⊓
        centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
      ext x
      exact ⟨fun hx => ⟨hx.1,(U_le_Z z |>.trans (Z_le_stabilizer d.radical z)) hx.2.1,hx.2.2⟩,
        fun hx => ⟨hx.1,hWU hx.1,hx.2.2⟩⟩
    rw [←inf_relIndex_left,heq,inf_relIndex_left]
    exact hidx
  exact (join_eq_of_equal_relative_index C D W hCW hbound (hDC.trans hWC.symm)).symm

/-- The same unequal terminal sequence has periodic full central kernels.
Its nonzero mutual kernel commutator has order q, lies in the preceding
critical commutator, and retains the complete joined edge intersection. -/
theorem Input.replacement_unequal_terminal_kernel_comparison
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) (hne : ¬ pathMoverAgreement (Nat.card F) p 0) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (unequalPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i, ¬ pathMoverAgreement (Nat.card F) (s i) 0) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, (Q d.radical (s (i+2)).last).relIndex (Z d.radical (s (i+2)).first)=Nat.card F ∧
        (Q d.radical (s (i+2)).first).relIndex (Z d.radical (s (i+2)).last)=Nat.card F) ∧
      (∀ i, let a := (s (i+3)).first
        let z := (s (i+3)).last
        let c := (s (i+2)).first
        ¬ Z d.radical a ⊓ Q d.radical z ≤ B d.radical c (geometry.Z_normal c)) ∧
      (∀ i, let a := (s (i+3)).first
        let z := (s (i+3)).last
        let c := (s (i+2)).first
        let e := (s (i+2)).last
        let E := Z d.radical a ⊓ Q d.radical z
        let D := ⁅E,Z d.radical e ⊓ Q d.radical c⁆
        (¬ Z d.radical e ≤ normalizer ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
        D ≠ ⊥ ∧ Nat.card F ≤ Nat.card D ∧
        ⁅E,X d.radical e ⊓ Q d.radical c⁆ = D ∧
        D = ⁅E,U d.radical e ⊓ Q d.radical c⁆) ∧
      (∀ i, let C := fun j => U d.radical (s j).first ⊓
          centralizer (stabilizer d.radical (s j).first : Set (FreeAmalgam d.radical))
        let D := ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆
        C (i+2)=C i ∧
        D ⊓ Z d.radical ((s (i+2)).path.walk.getVert 1)=C (i+2) ∧
        (∀ k, C (i+2) ≤ stabilizer d.radical (s (i+k)).first ⊓
          centralizer (stabilizer d.radical (s (i+k)).first : Set (FreeAmalgam d.radical)))) ∧
      (∀ i, let a := (s (i+3)).first
        let z := (s (i+3)).last
        let c := (s (i+2)).first
        let e := (s (i+2)).last
        let E := Z d.radical a ⊓ Q d.radical z
        let D := ⁅E,Z d.radical e ⊓ Q d.radical c⁆
        D ≤ E ⊓ U d.radical e ∧
        D ≤ ⁅Z d.radical c,Z d.radical e⁆ ∧ Nat.card D=Nat.card F ∧
        (D ⊔ ⁅Z d.radical a,Z d.radical z⁆) ⊓
          Z d.radical ((s (i+3)).path.walk.getVert 1) =
          U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
        ⁅Z d.radical c,Z d.radical e⁆ = D ⊔
          (U d.radical e ⊓ centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical))) ∧
        (1 ≤ i → geometry.b d.radical=6 → ⁅Z d.radical c,Z d.radical e⁆ ≤ Z d.radical a)) := by
  obtain ⟨s,hs0,hs,hne,hover,hdata,hnotB,hdisp⟩ :=
    h.replacement_unequal_terminal_normalizer_escape d p hb hne
  have hsat := unequal_terminal_saturation h d hb s hs
  refine ⟨s,hs0,hs,hne,hover,hdata,hnotB,hdisp,hsat,?_⟩
  intro i
  dsimp only
  obtain ⟨hnotnorm,hne,hlo,hX,hU⟩ := hdisp i
  obtain ⟨hic,hie⟩ := hdata i
  let a := (s (i+3)).first
  let z := (s (i+3)).last
  let c := (s (i+2)).first
  let e := (s (i+2)).last
  let E := Z d.radical a ⊓ Q d.radical z
  let Y := E ⊔ Z d.radical c
  let A := U d.radical e ⊓ Q d.radical c
  obtain ⟨w,hw,hcw,haw,hfirst⟩ := (hs (i+2)).choice
  have hEV : E ≤ V d.radical c := inf_le_left.trans
    (le_sup_left.trans (neighbor_seed_join_le_radius hcw haw))
  have hYV : Y ≤ V d.radical c := sup_le hEV (Z_le_VBall d.radical c 2)
  have hYQ : Y ≤ Q d.radical c := hYV.trans
    (geometry.V_le_Q (by omega) c (s (i+2)).path.start_color)
  have hdist : (cosetGraph d.radical).dist z e=2 := by
    simpa only [show i+2+1=i+3 by omega] using
      shifted_last_distance (unequalPathChoice geometry (Nat.card F)) s hs (i+2) 1 (by omega)
  have hES : E ≤ stabilizer d.radical e := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two z e (s (i+3)).path.end_color
      (s (i+2)).path.end_color hdist.le)
  have hYS : Y ≤ stabilizer d.radical e := sup_le hES
    (Z_le_stabilizer_of_dist_le c (geometry.exists_critical c (s (i+2)).path.start_color)
      (s (i+2)).path.critical.1.le)
  have hcQz : Z d.radical c ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt _ c (geometry.exists_critical c (s (i+2)).path.start_color)
    have hz := (hs (i+2)).last_eq
    simp only [show i+2+1=i+3 by omega] at hz
    dsimp only [c,z]
    rw [hz,(s (i+2)).path.dist_start (by rw [(s (i+2)).path.length_eq_b]; omega),
      geometry.distance_constant (s (i+2)).first (s (i+2)).path.start_color]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  have hYVz : Y ≤ V d.radical c ⊓ Q d.radical z :=
    le_inf hYV (sup_le inf_le_right hcQz)
  have hquad : ⁅⁅X d.radical e ⊓ Q d.radical c,Y⁆,Y⁆=⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl hYVz) hYVz).trans_eq
      (h.replacement_radius_commutator_bounds d geometry hb.le (s (i+2)).path.start_color e z).2)
  have hASa : A ≤ stabilizer d.radical a := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two c a (s (i+2)).path.start_color
      (s (i+3)).path.start_color (by
        rw [SimpleGraph.dist_comm]
        simpa only [show i+2+1=i+3 by omega] using
          (shifted_start_distance (unequalPathChoice geometry (Nat.card F)) s hs (i+2) 1 (by omega)).le))
  have heQz : U d.radical e ≤ Q d.radical z := by
    exact (U_le_Z e).trans (by
      apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e (s (i+2)).path.end_color)
      rw [geometry.distance_constant e (s (i+2)).path.end_color,SimpleGraph.dist_comm,hdist]
      change 2 < geometry.b d.radical; omega)
  have hANE : A ≤ normalizer (E : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change E.map (MulAut.conj x).toMonoidHom=E
    dsimp only [E]
    rw [map_inf _ _ _ (MulAut.conj x).injective,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (hASa hx)),
      mem_normalizer_iff_map_conj_eq.mp ((Q d.radical z).le_normalizer (heQz hx.1))]
  have hEU : ⁅E,Z d.radical e ⊓ Q d.radical c⁆ ≤ E ⊓ U d.radical e := by
    rw [hU]
    refine le_inf (le_normalizer_iff_commutator_le_left.mp hANE) ?_
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hES.trans (U_normalized e)))
  have hANY : A ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    (le_inf hANE ((inf_le_right.trans (fun _ hx => hx.1)).trans (Z_normalized d.radical c))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hbadY : ¬ ⁅Y,Z d.radical e⁆ ≤ Z d.radical c ⊔ ⁅Y,A⁆ := by
    intro hh
    apply hnotnorm
    exact le_normalizer_iff_commutator_le_left.mpr (hh.trans
      (sup_le le_sup_right (le_normalizer_iff_commutator_le_left.mp hANY)))
  have hsmall : (Q d.radical e).relIndex (Z d.radical c) < Nat.card F^2 := by
    rw [hic]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith
  have hfull := (h.replacement_root_intersection_fixed_and_commutator d
    (s (i+2)).path hb.le hsmall Y hYS).1
  have hbadfull : ¬ ⁅Y,Z d.radical e⁆ ≤ Z d.radical c ⊔
      ⁅Y,X d.radical e ⊓ Q d.radical c⁆ := by
    rw [hfull]; exact hbadY
  have hbound := h.replacement_critical_intersection_le_commutator_of_comparison d
    (s (i+2)).path hb.le Y le_sup_right hYQ hYS hquad hic hie hbadfull
  have hcard := h.replacement_critical_intersection_bound_of_comparison d
    (s (i+2)).path hb.le Y le_sup_right hYQ hYS hquad hic hie hbadfull
  rw [hfull] at hbound hcard
  have hsub : ⁅E,Z d.radical e ⊓ Q d.radical c⁆ ≤ ⁅Y,A⁆ := by
    rw [hU]
    exact commutator_mono le_sup_left le_rfl
  have hfin : ⁅Y,A⁆ ≤ U d.radical e := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYS.trans (U_normalized e)))
  let := finite_stabilizer d.radical e
  let : Finite (⁅Y,A⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion (hfin.trans ((U_le_Z e).trans (Z_le_stabilizer d.radical e)))) (inclusion_injective _)
  have hupper := (Nat.card_le_card_of_injective _ (inclusion_injective hsub)).trans hcard
  let D := ⁅E,Z d.radical e ⊓ Q d.radical c⁆
  let D₄ := ⁅Z d.radical a,Z d.radical z⁆
  let I := (D ⊔ D₄) ⊓ Z d.radical w
  have hDUa : D ≤ U d.radical a := by
    dsimp only [D,E,a,z,c,e]
    rw [hU]
    apply (commutator_mono inf_le_left le_rfl).trans
    rw [h.replacement_Z_commutator_eq_U d geometry hb.le (s (i+3)).path.start_color A hASa]
    exact le_normalizer_iff_commutator_le_left.mp (hASa.trans (U_normalized a))
  have hD₄Ua : D₄ ≤ U d.radical a := by
    dsimp only [D₄,a,z]
    rw [h.replacement_Z_commutator_eq_U d geometry hb.le (s (i+3)).path.start_color
      (Z d.radical (s (i+3)).last) ((s (i+3)).path.endpoint_Z_le_start_stabilizer (by omega))]
    exact le_normalizer_iff_commutator_le_left.mp
      (((s (i+3)).path.endpoint_Z_le_start_stabilizer (by omega)).trans (U_normalized a))
  have hIU : I ≤ U d.radical a := inf_le_left.trans (sup_le hDUa hD₄Ua)
  obtain ⟨v,hv,hav,hcv,hfirst₀⟩ := (hs (i+1)).choice
  obtain ⟨y,hy,hyv,hyw,hidx⟩ := hw.1
  have he := (hs (i+1)).overlap 0 (by omega)
  simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
  rw [he] at hyv
  have hwcol : color d.radical w=true := by
    have hn := adjacent_color_ne d.radical hcw
    rw [(s (i+2)).path.start_color] at hn
    cases hh : color d.radical w <;> simp_all
  have hgenC : stabilizer d.radical c ≤ Q d.radical w ⊔ Z d.radical e := hw.2.1.ge
  have hgen₀ : stabilizer d.radical (s (i+1)).first ≤ Q d.radical v ⊔ Z d.radical (s (i+1)).last := hv.2.1.ge
  let : IsElementaryAbelian 2 (Z d.radical e) := geometry.Z_elementary (by omega) e (s (i+2)).path.end_color
  have hDe : D ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
    (hEU.trans (inf_le_right.trans (U_le_Z e))).trans
      (commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr inferInstance))
  have hD₀ : D ≤ centralizer (Z d.radical (s (i+1)).last : Set (FreeAmalgam d.radical)) :=
    (hEU.trans (inf_le_right.trans (U_le_Z e))).trans
      (endpoint_seed_centralizes_nearby geometry hb (s (i+2)).path.end_color (s (i+1)).path.end_color (by
        have hh := shifted_last_distance (unequalPathChoice geometry (Nat.card F)) s hs (i+1) 1 (by omega)
        exact hh.le.trans (by decide)))
  have hD₄e : D₄ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) := by
    simpa only [show i+2+1=i+3 by omega] using
      shifted_commutator_centralizes_endpoint (unequalPathChoice geometry (Nat.card F)) s hs (i+2) 1 (by omega)
  have hD₄₀ : D₄ ≤ centralizer (Z d.radical (s (i+1)).last : Set (FreeAmalgam d.radical)) :=
    shifted_commutator_centralizes_endpoint (unequalPathChoice geometry (Nat.card F)) s hs (i+1) 2 (by omega)
  have hcent := (central_intersection_propagates I hwcol hcw hcv inf_le_right
    (inf_le_left.trans (sup_le hDe hD₄e)) (inf_le_left.trans (sup_le hD₀ hD₄₀))
    hgenC hgen₀ y (Ltilde_le_stabilizer _ hy) hyv.symm).2.2
  have hIeq : I=U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm (le_inf hIU hcent)
    have heq := (hsat (i+1)).2.1
    simp only [show i+1+2=i+3 by omega] at heq
    have hw' : (s (i+3)).path.walk.getVert 1=w := by
      simpa only [show i+2+1=i+3 by omega] using hfirst
    rw [hw'] at heq
    exact heq.symm.le.trans (inf_le_inf_right _ le_sup_right)
  have hIeq' : (D ⊔ D₄) ⊓ Z d.radical ((s (i+3)).path.walk.getVert 1) =
      U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hw' : (s (i+3)).path.walk.getVert 1=w := by
      simpa only [show i+2+1=i+3 by omega] using hfirst
    rw [hw']
    exact hIeq
  have hDcard : Nat.card (⁅E,Z d.radical e ⊓ Q d.radical c⁆ :
      Subgroup (FreeAmalgam d.radical))=Nat.card F := Nat.le_antisymm hupper hlo
  have hdecomp := h.replacement_critical_commutator_eq_intersection_join_kernel d
    (s (i+2)).path hb.le hie hic E hES (by rwa [hX])
    (by rw [hX]; exact hsub.trans hbound) (by rwa [hX])
  rw [hX] at hdecomp
  refine ⟨hEU,hsub.trans hbound,hDcard,hIeq',hdecomp,?_⟩
  intro hi hb6
  have hlast : e=(s (i-1)).first := by
    have hh := shifted_last_vertex (unequalPathChoice geometry (Nat.card F)) s hs
      (i-1) 3 (by omega)
    simpa only [show i-1+3=i+2 by omega,hb6,Nat.sub_self,SimpleGraph.Walk.getVert_zero] using hh
  have hcenter : U d.radical e ⊓ centralizer
      (stabilizer d.radical e : Set (FreeAmalgam d.radical)) ≤ Z d.radical a := by
    rw [hlast]
    have hp₁ := (hsat (i-1)).1
    have hp₂ := (hsat (i+1)).1
    simp only [show i-1+2=i+1 by omega] at hp₁
    simp only [show i+1+2=i+3 by omega] at hp₂
    rw [←hp₁,←hp₂]
    exact inf_le_left.trans (U_le_Z a)
  rw [hdecomp]
  exact sup_le (hEU.trans (inf_le_left.trans inf_le_left)) hcenter


private theorem generated_commutator_not_le_neighbor
    {geometry : Geometry d.radical} {c e a w : Vertex d.radical}
    (path : CriticalPath d.radical geometry c e) (hb : 4 ≤ geometry.b d.radical)
    (hcw : Adjacent d.radical c w) (haw : Adjacent d.radical a w)
    (ha : color d.radical a=false)
    (hi : (Q d.radical c).relIndex (Z d.radical e)=Nat.card F)
    (hne : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical c)
        (Q d.radical c) (Q d.radical w) (Nat.card F^2))
    (hres : Ltilde d.radical c ≤ Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical e) :
    ¬ ⁅Z d.radical c,Z d.radical e⁆ ≤ Z d.radical a := by
  intro hle
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical w) (Nat.card F^2)
  let I := Z d.radical c ⊓ Z d.radical a
  let S := stabilizer d.radical c
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 c (adjacent_symm _ hcw))
  have hJSa : J ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ haw))
  have hR : ⁅Z d.radical c,Z d.radical e⁆ ≤ I :=
    le_inf (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path) hle
  have hJN : J ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    (le_inf (hJS.trans (Z_normalized d.radical c))
      (hJSa.trans (Z_normalized d.radical a))).trans inf_normalizer_le_normalizer_inf
  have hEN : Z d.radical e ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono inf_le_left le_rfl).trans hR)
  have hLN := hres.trans (sup_le hJN hEN)
  have hQN : Q d.radical c ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c path.start_color))).trans
      (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hlocal : Ltilde d.radical c ⊔ Q d.radical c=S := by
    obtain ⟨i,hinj,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hSN : S ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    hlocal.ge.trans (sup_le hLN hQN)
  obtain ⟨E,hE,f,hf,hfQ,hrest⟩ := h.replacement_inner_natural_action d geometry hb path.start_color
  let Z₀ := (Z d.radical c).subgroupOf S
  let I₀ := I.subgroupOf S
  let T := (Z d.radical e).subgroupOf S
  have hZcS : Z d.radical c ≤ S := Z_le_stabilizer d.radical c
  have hIS : I ≤ S := inf_le_left.trans hZcS
  have hES : Z d.radical e ≤ S := path.endpoint_Z_le_start_stabilizer (by omega)
  let : Z₀.Normal := (normal_subgroupOf_iff_le_normalizer hZcS).mpr (Z_normalized d.radical c)
  let : I₀.Normal := (normal_subgroupOf_iff_le_normalizer hIS).mpr hSN
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : IsPGroup 2 f.ker := by
    have hp := Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) c path.start_color
    exact (hfQ.symm ▸ hp).of_injective
      (f.ker.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom
      (f.ker.equivMapOfInjective S.subtype S.subtype_injective).injective
  have hT : ¬ T ≤ f.ker := by
    intro hh
    have hm := map_mono (f := S.subtype) hh
    rw [map_subgroupOf_eq_of_le hES,hfQ] at hm
    have hone := relIndex_eq_one.mpr hm
    rw [hi] at hone
    exact (Finite.one_lt_card (α := F)).ne' hone
  have hc : ⁅Z₀,T⁆ ≤ I₀ := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hZcS,
      map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hIS]
    exact hR
  have hwhole := commutator_pResidual_le_of_simple_kernel_escape 2 f hf hk Z₀ I₀ T hT hc
  have hUI : U d.radical c ≤ I := by
    have hh := map_mono (f := S.subtype) hwhole
    rwa [map_commutator,map_subgroupOf_eq_of_le hZcS,map_subgroupOf_eq_of_le hIS] at hh
  have hsmall := (h.replacement_unequal_original_quadratic d geometry hb ha haw hcw hne.symm).1
  have hbig := (h.replacement_unequal_individual_indices d geometry hb path.start_color hcw haw hne).2
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a ha
  let := finite_Z d.radical a
  have hfull := fixed_index_of_split (Z d.radical a) (U d.radical a)
    (Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    J (U_le_Z a) (h.replacement_Z_eq_U_sup_fixed d geometry hb ha)
    (inf_le_right.trans (centralizer_le hJSa))
  have hidx := (centralizer (J : Set (FreeAmalgam d.radical))).relIndex_le_of_le_right
    (hUI.trans inf_le_right) index_ne_zero_of_finite
  rw [hfull,hsmall] at hidx
  exact hbig.not_ge hidx

/-- Unequal neighboring movers cannot occur at critical distance six.
The same selected sequence forces a full critical commutator into the next
seed. Residual invariance then forces the full moving layer into that seed,
contradicting its unequal mover's strictly larger fixed index. -/
theorem Input.replacement_unequal_distance_ne_six
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hne : ¬ pathMoverAgreement (Nat.card F) p 0) :
    geometry.b d.radical ≠ 6 := by
  intro hb6
  have hb : 4 < geometry.b d.radical := by omega
  obtain ⟨s,hs0,hs,hsne,hover,hindices,hnotB,hdisp,hsat,hcomparison⟩ :=
    h.replacement_unequal_terminal_kernel_comparison d p hb hne
  obtain ⟨w,hw,hcw,haw,hfirst⟩ := (hs 3).choice
  change (s 4).path.walk.getVert 1=w at hfirst
  have hsecond : (s 4).path.walk.getVert 2=(s 3).first := by
    have hh := (hs 3).overlap 0 (by omega)
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hh
  have hne' : Subgroup.SmallMover.join (U d.radical (s 4).first)
      (Q d.radical (s 4).first) (Q d.radical w) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical (s 3).first)
        (Q d.radical (s 3).first) (Q d.radical w) (Nat.card F^2) := by
    have hn := hsne 4
    simp only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,
      SimpleGraph.Walk.getVert_zero,hfirst,hsecond] at hn
    exact fun he => hn he.symm
  have hres : Ltilde d.radical (s 3).first ≤
      Subgroup.SmallMover.join (U d.radical (s 4).first)
        (Q d.radical (s 4).first) (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical (s 3).last := by
    rcases hw.2.2.2 with hh | hh
    · exact hh
    · exact False.elim (hh (h.replacement_unequal_terminal_X_decomposition d p hb hne
        (s 3).path.start_color))
  have hle : ⁅Z d.radical (s 3).first,Z d.radical (s 3).last⁆ ≤ Z d.radical (s 4).first :=
    (hcomparison 1).2.2.2.2.2 (by decide) hb6
  exact generated_commutator_not_le_neighbor h d (s 3).path hb.le hcw haw
    (s 4).path.start_color (hindices 1).2 hne' hres hle

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
