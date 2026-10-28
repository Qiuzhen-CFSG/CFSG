module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Image
public import Theory.GroupTheory.CoprimeCentralizerImageDecomposition
public import Theory.Representation.NormalInvariants

/-!
# Coprime splitting through the actual tilded action

The action of a center-centralizing subgroup on U-tilde has the same
kernel as its terminal dotted action, using the original tilde-kernel
calculation. Its elementary-nine image therefore gives a coprime direct
sum. For a nontrivial normal image in the irreducible hatted action,
normal invariants vanish; the actual equivariant projection identifies
the fixed summand with the image of Z(U).

Source: Aschbacher--Smith 14.3.15, printed p.995.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {V : Subgroup G} {L M : Subgroup G}

theorem terminal_tilde_actor_range_card
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V] (d : ClosureGeometry F)
    (A : Subgroup G) (hAH : A ≤ F.H) (hAC : A ≤ centralizer (F.ZU : Set G)) :
    Nat.card ((F.tilde F.U).normalizerMonoidHom.comp
      (inclusion (F.tilde_normalizes A F.U
        (hAH.trans (le_normalizer_conjugateSpanBy _ _))))).range =
      Nat.card (F.terminalDot A) := by
  let a := (F.tilde F.U).normalizerMonoidHom.comp
    (inclusion (F.tilde_normalizes A F.U (hAH.trans (le_normalizer_conjugateSpanBy _ _))))
  let i := inclusion hAH
  let f : A →* MulAut (F.tilde F.U) := (F.localTildeAction F.H le_rfl).comp i
  let q := (QuotientGroup.mk' F.terminalHatAction.ker).comp i
  have hcomp : a.comp (F.tildeMap A hAH) = f := by
    ext x u
    rfl
  have hqrange : q.range = F.terminalDot A := by
    change ((QuotientGroup.mk' F.terminalHatAction.ker).comp (inclusion hAH)).range = _
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hfker : f.ker = q.ker := by
    change ((F.localTildeAction F.H le_rfl).comp i).ker =
      ((QuotientGroup.mk' F.terminalHatAction.ker).comp i).ker
    rw [←MonoidHom.comap_ker,←MonoidHom.comap_ker,QuotientGroup.ker_mk',d.tilde_kernel]
    ext x
    have hx : i x ∈ A.subgroupOf F.H := x.property
    have hh := terminal_restricted_kernel_eq_core F d A hAC
    constructor
    · intro h
      exact (hh.symm ▸ (show i x ∈ A.subgroupOf F.H ⊓ pCore 2 F.H from ⟨hx,h⟩)).2
    · intro h
      exact (hh ▸ (show i x ∈ A.subgroupOf F.H ⊓ F.terminalHatAction.ker from ⟨hx,h⟩)).2
  have harange : f.range = a.range := by
    calc
      f.range = (a.comp (F.tildeMap A hAH)).range := congrArg MonoidHom.range hcomp.symm
      _ = a.range := by
        rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (F.tildeMap_surjective A hAH)]
        exact (MonoidHom.range_eq_map a).symm
  calc
    Nat.card a.range = Nat.card f.range := congrArg (fun J : Subgroup (MulAut (F.tilde F.U)) => Nat.card J) harange.symm
    _ = f.ker.index := (index_ker f).symm
    _ = q.ker.index := congrArg Subgroup.index hfker
    _ = Nat.card (F.terminalDot A) := (index_ker q).trans (congrArg (fun J : Subgroup F.TerminalHdot => Nat.card J) hqrange)

theorem terminal_tilde_center_residual_splitting
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V] (d : ClosureGeometry F)
    (g : G) (hg : conjugate F.ZU g ≤ F.H)
    (hc : ⁅F.ZU,conjugate F.ZU g⁆ = ⊥)
    (h9 : Nat.card (F.terminalDot (centerConjugateResidual F g)) = 9) :
    F.tilde F.U = ⁅F.tilde F.U,F.tilde (centerConjugateResidual F g)⁆ ⊔
      (F.tilde F.U ⊓ centralizer (F.tilde (centerConjugateResidual F g) : Set F.G₁tilde)) ∧
    Disjoint ⁅F.tilde F.U,F.tilde (centerConjugateResidual F g)⁆ (F.tilde F.ZU) := by
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point d.two d.frattini_point
  have hAH := centerConjugateResidual_le_H F g hg
  have hAC := centerConjugateResidual_centralizes F g hc
  have hn := F.tilde_normalizes (centerConjugateResidual F g) F.U
    (hAH.trans (le_normalizer_conjugateSpanBy _ _))
  have hcop : Nat.Coprime
      (Nat.card ((F.tilde F.U).normalizerMonoidHom.comp (inclusion hn)).range)
      (Nat.card (F.tilde F.U)) := by
    rw [terminal_tilde_actor_range_card F d _ hAH hAC,h9]
    obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp
      (IsElementaryAbelian.isPGroup 2 (F.tilde F.U))
    rw [hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  refine ⟨eq_commutator_sup_centralizer_of_actionRange_coprime _ _ hn hcop,?_⟩
  apply (commutator_disjoint_centralizer_of_actionRange_coprime _ _ hn hcop).mono_right
  refine le_inf (map_mono (comap_mono (map_subtype_le (center F.U)))) ?_
  have hz : F.ZU ≤ centralizer (centerConjugateResidual F g : Set G) :=
    le_centralizer_iff.mpr hAC
  have ht : (F.ZU.subgroupOf F.H) ≤
      centralizer ((centerConjugateResidual F g).subgroupOf F.H : Set F.H) := by
    intro z hz'
    rw [mem_centralizer_iff]
    intro a ha
    apply F.H.subtype_injective
    exact (mem_centralizer_iff.mp (hz hz')) a ha
  apply (map_mono ht).trans
  change (centralizer ((centerConjugateResidual F g).subgroupOf F.H : Set F.H)).map F.tildeProjection ≤
    centralizer (((centerConjugateResidual F g).subgroupOf F.H).map F.tildeProjection : Set _)
  rw [coe_map]
  exact map_centralizer_le_centralizer_image _ _

omit [Finite G] in
theorem terminal_tilde_fixed_actor_eq_center
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    [Representation.IsIrreducible F.terminalRepresentation]
    (A : Subgroup G) (hAH : A ≤ F.H) (hHA : F.H ≤ normalizer (A : Set G))
    (hAC : A ≤ centralizer (F.ZU : Set G)) (hne : F.terminalDot A ≠ ⊥) :
    F.tilde F.U ⊓ centralizer (F.tilde A : Set F.G₁tilde) = F.tilde F.ZU := by
  let N := F.terminalDot A
  let : (A.subgroupOf F.H).Normal := (normal_subgroupOf_iff_le_normalizer hAH).mpr hHA
  let : N.Normal := Normal.map inferInstance (QuotientGroup.mk' F.terminalHatAction.ker)
    (QuotientGroup.mk'_surjective _)
  have hfix : Representation.invariants (F.terminalRepresentation.comp N.subtype) = ⊥ := by
    by_contra hh
    have hk := Representation.le_ker_of_normal_invariants_ne_bot F.terminalRepresentation N hh
    apply hne
    exact bot_unique (hk.trans_eq ((MonoidHom.ker_eq_bot_iff _).mpr F.terminalRepresentation_injective))
  apply le_antisymm
  · intro u hu
    let a : F.tilde F.U := ⟨u,hu.1⟩
    let q := F.tildeToUhat (by decide : 1 ≤ 2)
    have hv : Additive.ofMul (q a) ∈ Representation.invariants
        (F.terminalRepresentation.comp N.subtype) := by
      rintro ⟨r,hr⟩
      obtain ⟨k,hk,rfl⟩ := hr
      have ht : F.tildeProjection k ∈ F.tilde A := mem_map_of_mem _ hk
      have ha : F.localTildeAction F.H le_rfl k a = a := by
        apply Subtype.ext
        change F.tildeProjection k * u * (F.tildeProjection k)⁻¹ = u
        rw [mem_centralizer_iff.mp hu.2 _ ht,mul_assoc,mul_inv_cancel,mul_one]
      apply Additive.toMul.injective
      change F.uhatAction k (q a) = q a
      exact (F.tildeToUhat_equivariant (by decide) k a).symm.trans (congrArg q ha)
    have hz : Additive.ofMul (q a) = 0 := by
      simpa only [hfix,Submodule.mem_bot] using hv
    have ha : a ∈ q.ker := congrArg Additive.toMul hz
    rw [show q.ker = (F.tilde F.ZU).subgroupOf (F.tilde F.U) from
      F.tildeToUhat_ker (by decide)] at ha
    exact ha
  · refine le_inf (map_mono (comap_mono (map_subtype_le (center F.U)))) ?_
    have hz : F.ZU ≤ centralizer (A : Set G) := le_centralizer_iff.mpr hAC
    have ht : F.ZU.subgroupOf F.H ≤ centralizer (A.subgroupOf F.H : Set F.H) := by
      intro z hz'
      rw [mem_centralizer_iff]
      intro a ha
      apply F.H.subtype_injective
      exact mem_centralizer_iff.mp (hz hz') a ha
    apply (map_mono ht).trans
    change (centralizer (A.subgroupOf F.H : Set F.H)).map F.tildeProjection ≤
      centralizer ((A.subgroupOf F.H).map F.tildeProjection : Set F.G₁tilde)
    rw [coe_map]
    exact map_centralizer_le_centralizer_image _ _


/-- The normal odd image has no fixed vector in the irreducible hatted action;
its fixed part in the original tilded group is therefore exactly the center. -/
theorem terminal_tilde_center_residual_direct_sum
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    [Representation.IsIrreducible F.terminalRepresentation]
    (d : ClosureGeometry F) (g : G) (hg : conjugate F.ZU g ≤ F.H)
    (hc : ⁅F.ZU,conjugate F.ZU g⁆ = ⊥)
    (h9 : Nat.card (F.terminalDot (centerConjugateResidual F g)) = 9) :
    F.tilde F.U = ⁅F.tilde F.U,F.tilde (centerConjugateResidual F g)⁆ ⊔ F.tilde F.ZU ∧
      Disjoint ⁅F.tilde F.U,F.tilde (centerConjugateResidual F g)⁆ (F.tilde F.ZU) := by
  have hn : F.terminalDot (centerConjugateResidual F g) ≠ ⊥ := by
    intro hb
    rw [hb,card_bot] at h9
    omega
  obtain ⟨hs,hd⟩ := terminal_tilde_center_residual_splitting F d g hg hc h9
  rw [terminal_tilde_fixed_actor_eq_center F _ (centerConjugateResidual_le_H F g hg)
    (centerConjugateResidual_normalized F g) (centerConjugateResidual_centralizes F g hc) hn] at hs
  exact ⟨hs,hd⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
