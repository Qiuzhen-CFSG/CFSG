module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Markers
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Cardinalities
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The actual five-point line action and a source edge element

Projection to the second factor of the original marked normalizer quotient
has kernel K and image S₅. The literal point stabilizer has index five and
contains K. Its normal core modulo K is trivial: a nontrivial normal subgroup
of S₅ would contain A₅, contradicting that index. Consequently the action on
the five ambient incident points induces their entire symmetric group.

The factor S supplies every such permutation. A lifted transposition gives
an actual element t in H∩N outside M whose square belongs to M, and the full
five-point action proves the required `Cosets.LineTransitive` clause.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.1)(1), pp.599–600,
DOI 10.1007/BF01232280. This proves that the five-point kernel is K;
the seven-plane kernel is the distinct group S.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups
open SourceCycleBase GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)
attribute [local instance] ThreeSpaceData.R_normal_in_normalizer ThreeSpaceData.R_normal_in_S_intrinsic

/-- The five-point quotient, retaining the original S/R marking. -/
noncomputable def lineProjection : a.L.G₂ →* Equiv.Perm (Fin 5) :=
  (MonoidHom.snd (MulAut a.d.space) (Equiv.Perm (Fin 5))).comp
    ((a.d.markedNormalizerQuotientEquiv h).toMonoidHom.comp
      ((QuotientGroup.mk' _).comp (MulEquiv.subgroupCongr a.line_normalizer).toMonoidHom))

theorem lineProjection_product (k : a.d.K) (s : a.d.S) (n : a.L.G₂)
    (hn : (n : G) = (k : G)*(s : G)) :
    a.lineProjection n = a.d.SQuotientEquiv h (QuotientGroup.mk' _ s) := by
  change (a.d.markedNormalizerQuotientEquiv h
    (QuotientGroup.mk' _ ((MulEquiv.subgroupCongr a.line_normalizer) n))).2 = _
  have he : (MulEquiv.subgroupCongr a.line_normalizer) n =
      (⟨(k : G)*(s : G), (normalizer (a.d.space : Set G)).mul_mem
        (a.d.K_le_normalizer k.property) ((Subgroup.centralizer_le_normalizer _) s.property)⟩ :
          normalizer (a.d.space : Set G)) := Subtype.ext hn
  rw [he,a.d.markedNormalizerQuotientEquiv_product]

theorem lineProjection_surjective : Function.Surjective a.lineProjection := by
  intro p
  obtain ⟨s,hs⟩ := QuotientGroup.mk'_surjective (a.d.R.subgroupOf a.d.S)
    ((a.d.SQuotientEquiv h).symm p)
  let n : a.L.G₂ := ⟨s, a.line_normalizer.symm ▸ (Subgroup.centralizer_le_normalizer _) s.property⟩
  refine ⟨n,?_⟩
  rw [a.lineProjection_product 1 s n (by simp [n]),hs,MulEquiv.apply_symm_apply]

theorem lineProjection_ker : a.lineProjection.ker = a.d.K.subgroupOf a.L.G₂ := by
  ext n
  obtain ⟨k,hk,s,hs,hns⟩ := a.d.normalizer_product h (n : G) (a.line_normalizer ▸ n.property)
  have he := a.lineProjection_product ⟨k,hk⟩ ⟨s,hs⟩ n hns.symm
  change a.lineProjection n = 1 ↔ (n : G) ∈ a.d.K
  rw [he]
  have hmem : a.d.SQuotientEquiv h (QuotientGroup.mk' _ (⟨s,hs⟩ : a.d.S)) = 1 ↔ s ∈ a.d.R := by
    rw [map_eq_one_iff _ (a.d.SQuotientEquiv h).injective]
    exact QuotientGroup.eq_one_iff _
  rw [hmem,hns.symm]
  constructor
  · intro hr
    exact a.d.K.mul_mem hk hr.1
  · intro hks
    have hsk : s ∈ a.d.K := by
      simpa only [inv_mul_cancel_left] using a.d.K.mul_mem (a.d.K.inv_mem hk) hks
    exact ⟨hsk,hs⟩

theorem K_le_point : a.d.K ≤ a.P.M := by
  rw [←a.K_image]
  exact a.L.linear_le_point_line.trans inf_le_left

/-- The kernel of the literal five-point coset action is exactly K. -/
theorem point_line_normalCore :
    (a.P.M.subgroupOf a.L.G₂).normalCore = a.d.K.subgroupOf a.L.G₂ := by
  let U := a.P.M.subgroupOf a.L.G₂
  let f := a.lineProjection
  have hkU : f.ker ≤ U := by
    rw [a.lineProjection_ker]
    exact fun n hn => a.K_le_point hn
  have hindex : (U.map f).index = 5 := by
    rw [index_map,f.range_eq_top_of_surjective a.lineProjection_surjective,
      index_top,mul_one,sup_of_le_left hkU]
    exact a.point_line_index
  have hzero : U.normalCore.map f = ⊥ := by
    let : (U.normalCore.map f).Normal :=
      Subgroup.Normal.map inferInstance f a.lineProjection_surjective
    by_contra hn
    have ha : alternatingGroup (Fin 5) ≤ U.map f :=
      (Equiv.Perm.alternatingGroup_le_of_normal (by simp)
        ((nontrivial_iff_ne_bot _).mpr hn)).trans (map_mono U.normalCore_le)
    have hd := index_dvd_of_le ha
    have hai : (alternatingGroup (Fin 5)).index = 2 := by
      have hc := (alternatingGroup (Fin 5)).card_mul_index
      rw [nat_card_alternatingGroup,Nat.card_perm,Nat.card_fin] at hc
      norm_num [Nat.factorial] at hc ⊢
    rw [hindex,hai] at hd
    norm_num at hd
  have he : U.normalCore = f.ker := le_antisymm
    ((Subgroup.map_eq_bot_iff _).mp hzero) (normal_le_normalCore.mpr hkU)
  exact he.trans a.lineProjection_ker

/-- Source (5.1)(1), for the actual points incident with the original line. -/
theorem point_action_kernel (g : a.L.G₂) :
    (∀ x : Point a.P, OnLine a.L x (Cosets.vertex a.L.G₂ 1) →
      (g : G) • x = x) ↔ (g : G) ∈ a.d.K := by
  have hk : g ∈ (a.P.M.subgroupOf a.L.G₂).normalCore ↔ (g : G) ∈ a.d.K := by
    rw [a.point_line_normalCore]; rfl
  rw [←hk]
  constructor
  · intro hg n
    have hx : OnLine a.L (Cosets.vertex a.P.M (n : G)⁻¹) (Cosets.vertex a.L.G₂ 1) :=
      ⟨(n : G)⁻¹,rfl,(Cosets.vertex_eq_base _ _).mpr (a.L.G₂.inv_mem n.property)⟩
    have he := hg _ hx
    rw [Cosets.smul_vertex] at he
    have hm := (Cosets.vertex_eq_iff a.P.M (n : G)⁻¹ ((g : G)*(n : G)⁻¹)).mp he.symm
    change (n : G)*(g : G)*(n : G)⁻¹ ∈ a.P.M
    simpa only [inv_inv,mul_assoc] using hm
  · intro hg x hx
    obtain ⟨n,rfl,hn⟩ := hx
    have hnN := (Cosets.vertex_eq_base _ _).mp hn
    rw [Cosets.smul_vertex]
    apply Eq.symm
    apply (Cosets.vertex_eq_iff a.P.M n ((g : G)*n)).mpr
    have hm := hg (⟨n⁻¹,a.L.G₂.inv_mem hnN⟩ : a.L.G₂)
    change n⁻¹*(g : G)*(n⁻¹)⁻¹ ∈ a.P.M at hm
    simpa only [inv_inv,mul_assoc] using hm


abbrev LinePoints := {x : Point a.P // OnLine a.L x (Cosets.vertex a.L.G₂ 1)}

private theorem linePoint_smul (g : a.L.G₂) (x : a.LinePoints) :
    OnLine a.L ((g : G) • x.val) (Cosets.vertex a.L.G₂ 1) := by
  have he : (g : G) • Cosets.vertex a.L.G₂ 1 = Cosets.vertex a.L.G₂ 1 := by
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr g.property
  simpa only [OnLine,he] using incident_smul (g : G) x.property

/-- The literal action on the five ambient points of the original line. -/
noncomputable def linePointAction : a.L.G₂ →* Equiv.Perm a.LinePoints where
  toFun g := {
    toFun x := ⟨(g : G) • x.val,a.linePoint_smul g x⟩
    invFun x := ⟨(g⁻¹ : a.L.G₂) • x.val,a.linePoint_smul g⁻¹ x⟩
    left_inv x := Subtype.ext (inv_smul_smul (g : G) x.val)
    right_inv x := Subtype.ext (smul_inv_smul (g : G) x.val) }
  map_one' := Equiv.ext fun x => Subtype.ext (one_smul G x.val)
  map_mul' g k := Equiv.ext fun x => Subtype.ext (mul_smul (g : G) (k : G) x.val)

theorem linePointAction_apply (g : a.L.G₂) (x : a.LinePoints) :
    (a.linePointAction g x).val = (g : G) • x.val := by rfl

theorem linePointAction_ker : a.linePointAction.ker = a.d.K.subgroupOf a.L.G₂ := by
  ext g
  change a.linePointAction g = 1 ↔ (g : G) ∈ a.d.K
  rw [←a.point_action_kernel]
  constructor
  · intro hg x hx
    exact congrArg Subtype.val (Equiv.congr_fun hg (⟨x,hx⟩ : a.LinePoints))
  · intro hg
    apply Equiv.ext
    intro x
    exact Subtype.ext (hg x.val x.property)

/-- The original line group induces every permutation of its actual five points. -/
theorem linePointAction_surjective : Function.Surjective a.linePointAction := by
  have hker : a.linePointAction.ker = a.lineProjection.ker :=
    a.linePointAction_ker.trans a.lineProjection_ker.symm
  have hcard : Nat.card a.linePointAction.range = 120 := by
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange a.linePointAction).toEquiv,
      hker,Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective a.lineProjection a.lineProjection_surjective).toEquiv,
      Nat.card_perm,Nat.card_fin]
    norm_num [Nat.factorial]
  have ht : Nat.card (Equiv.Perm a.LinePoints) = 120 := by
    rw [Nat.card_perm,show Nat.card a.LinePoints = 5 from a.line_card _]
    norm_num [Nat.factorial]
  apply MonoidHom.range_eq_top.mp
  exact Subgroup.eq_top_of_card_eq _ (hcard.trans ht.symm)

private def baseLinePoint : a.LinePoints := ⟨Cosets.vertex a.P.M 1,⟨1,rfl,rfl⟩⟩

/-- The source centralizer factor already induces the full five-point action. -/
theorem exists_S_linePointAction (p : Equiv.Perm a.LinePoints) :
    ∃ (s : a.d.S) (n : a.L.G₂), (n : G) = s ∧ a.linePointAction n = p := by
  obtain ⟨n,hn⟩ := a.linePointAction_surjective p
  obtain ⟨k,hk,s,hs,hns⟩ := a.d.normalizer_product h (n : G) (a.line_normalizer ▸ n.property)
  let k' : a.L.G₂ := ⟨k,a.line_normalizer.symm ▸ a.d.K_le_normalizer hk⟩
  let s' : a.L.G₂ := ⟨s,a.line_normalizer.symm ▸ (Subgroup.centralizer_le_normalizer _) hs⟩
  have hk' : a.linePointAction k' = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [a.linePointAction_ker]
    exact hk
  have hns' : k'*s' = n := Subtype.ext hns
  refine ⟨⟨s,hs⟩,s',rfl,?_⟩
  rw [←hn,←hns',map_mul,hk',one_mul]

/-- The actual five-point action is doubly transitive in the source convention. -/
theorem line_transitive (t : G) (htN : t ∈ a.L.G₂) (htM : t ∉ a.P.M) :
    Cosets.LineTransitive a.P.M t a.L.G₂ := by
  classical
  intro u huN huM
  let b := a.baseLinePoint
  let y : a.LinePoints := ⟨Cosets.vertex a.P.M t,⟨t,rfl,(Cosets.vertex_eq_base _ _).mpr htN⟩⟩
  let v : a.LinePoints := ⟨Cosets.vertex a.P.M u,⟨u,rfl,(Cosets.vertex_eq_base _ _).mpr huN⟩⟩
  have hyb : y ≠ b := fun he => htM ((Cosets.vertex_eq_base _ _).mp (congrArg Subtype.val he))
  have hvb : v ≠ b := fun he => huM ((Cosets.vertex_eq_base _ _).mp (congrArg Subtype.val he))
  obtain ⟨p,hp⟩ := a.linePointAction_surjective (Equiv.swap y v)
  have hb : a.linePointAction p b = b := by
    rw [hp,Equiv.swap_apply_of_ne_of_ne hyb.symm hvb.symm]
  have hy : a.linePointAction p y = v := by rw [hp,Equiv.swap_apply_left]
  refine ⟨p,p.property,?_,?_⟩
  · have he := congrArg Subtype.val hb
    change (p : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 at he
    simpa only [Cosets.smul_vertex,mul_one] using he
  · exact congrArg Subtype.val hy

/-- A lift of a transposition supplies the literal source edge element.
Its square fixes the original point; its lift lies in S≤H∩N. -/
theorem exists_edge_element : ∃ t : G,
    t ∈ centralizer z ∧ t ∈ a.L.G₂ ∧ t ∉ a.P.M ∧ t*t ∈ a.P.M ∧
      Cosets.LineTransitive a.P.M t a.L.G₂ := by
  classical
  have hcard : Nat.card a.LinePoints = 5 := a.line_card _
  have : Nontrivial a.LinePoints := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let b := a.baseLinePoint
  obtain ⟨y,hy⟩ := exists_ne b
  obtain ⟨s,n,hns,hn⟩ := a.exists_S_linePointAction (Equiv.swap b y)
  have hny : a.linePointAction n b = y := by rw [hn,Equiv.swap_apply_left]
  have hnot : (n : G) ∉ a.P.M := by
    intro hm
    apply hy
    apply Subtype.ext
    have he := congrArg Subtype.val hny
    change (n : G) • Cosets.vertex a.P.M 1 = y.val at he
    rw [Cosets.smul_vertex,mul_one,(Cosets.vertex_eq_base _ _).mpr hm] at he
    exact he.symm
  have hsq : (n : G)*(n : G) ∈ a.P.M := by
    have he : a.linePointAction (n*n) b = b := by
      rw [map_mul,hn]
      simp
    have hv := congrArg Subtype.val he
    change ((n : G)*(n : G)) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 at hv
    rw [Cosets.smul_vertex,mul_one] at hv
    exact (Cosets.vertex_eq_base _ _).mp hv
  refine ⟨n,?_,n.property,hnot,hsq,a.line_transitive n n.property hnot⟩
  rw [hns]
  exact mem_centralizer_singleton_iff.mpr (s.property z (a.d.markedPoint 0).property).symm

end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
