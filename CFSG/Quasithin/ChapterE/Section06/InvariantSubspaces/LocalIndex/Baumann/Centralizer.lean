module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Reduction
public import Theory.GroupAction.PPerfectFixedCentralizer
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The centralizer of one normal short block

For a normal chi-zero block L with H = LR and R Sylow two in H, we prove
C_H(U(L)) = O₂(H). In fact the argument uses only the short-group clauses
of the block hypothesis, together with characteristic two in H.

For the inclusion O₂(H) ≤ C_H(U), put Q = O₂(H) and W = C_U(Q).
The commutator [Q,L] lies in O₂(L), so the Q- and L-actions on U commute.
Irreducibility of U/C_U(L) gives either W ≤ C_U(L) or U = W C_U(L).
In the first case the Thompson A × B fixed-point lemma would make L fix U,
contradicting [U,L] = U ≠ 1. In the second, [U,L] = U gives U ≤ W.

For the other inclusion, characteristic two descends from H to L.
The subgroup C_L(U) fixes both U and O₂(L)/U; its two-residual therefore
centralizes O₂(L), and characteristic two makes C_L(U) a two-group.
The quotient H/L is a two-group, so C_H(U) is also a two-group. It is
normal in H, and hence lies in O₂(H).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.11, printed pp.123–124 (PDF pp.134–135). The fixed-point argument is
the Thompson A × B step in the proof of A.1.41, printed p.31.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer of the core commutator is a two-group in characteristic two. -/
private theorem intrinsic_centralizer_le_core {X : Type*} [Group X] [Finite X]
    (hc : HasCharacteristicTwo X) :
    centralizer (ChapterC.blockU X : Set X) ≤ pCore 2 X := by
  let C := centralizer (ChapterC.blockU X : Set X)
  have hres : (pResidual 2 C).map C.subtype ≤ pCore 2 X := by
    apply le_trans (residual_centralizes_of_two_layer C (pCore 2 X)
      (ChapterC.blockU X) (pCore_isPGroup.to_le ChapterC.blockU_le_core) le_rfl ?_) hc
    rw [commutator_comm]
    exact commutator_mono le_rfl le_top
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨n, hn⟩ := isPGroup_quotient_pResidual (G := C) 2
      (QuotientGroup.mk' (pResidual 2 C) c)
    have hcr : c ^ 2 ^ n ∈ pResidual 2 C := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pResidual 2 C) (c ^ 2 ^ n) = 1
      rwa [map_pow]
    have hcc : (c : X) ^ 2 ^ n ∈ pCore 2 X := hres (mem_map_of_mem C.subtype hcr)
    obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := X)) ⟨_, hcc⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    change (c : X) ^ 2 ^ (n + m) = 1
    rw [pow_add, pow_mul]
    exact congrArg Subtype.val hm
  exact le_sSup ⟨inferInstance, hCp⟩

/-- A two-subgroup normalized by a short group and normalizing it centralizes its layer. -/
private theorem short_core_centralizes {L Q : Subgroup G}
    (hL : ChapterC.IsShort L) (hQ : IsPGroup 2 Q)
    (hLQ : L ≤ normalizer (Q : Set G))
    (hQL : Q ≤ normalizer (L : Set G)) : Q ≤ centralizer (U L : Set G) := by
  let V := U L
  let W := V ⊓ centralizer (Q : Set G)
  let Z := (ChapterC.blockU L ⊓ center L).map L.subtype
  have hVL : V ≤ L := map_subtype_le _
  have hLV : L ≤ normalizer (V : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  have hQV : Q ≤ normalizer (V : Set G) :=
    hQL.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  have hLW : L ≤ normalizer (W : Set G) :=
    (le_inf hLV (hLQ.trans (normalizer_le_normalizer_centralizer Q))).trans
      inf_normalizer_le_normalizer_inf
  have hWL : W ≤ L := inf_le_left.trans hVL
  have hcore : ⁅Q, L⁆ ≤ pCoreIn 2 L :=
    le_pCoreIn_of_normalizes
      (hQ.to_le (le_normalizer_iff_commutator_le_left.mp hLQ))
      (le_normalizer_iff_commutator_le_right.mp hQL)
      (normalizer_commutator_ge_right Q L)
  have hcomm : ⁅Q, L⁆ ≤ centralizer (V : Set G) := by
    apply hcore.trans
    exact (map_mono hL.core_centralizes_blockU).trans
      (map_centralizer_le_centralizer_image _ L.subtype)
  have hVLcomm : ⁅V, L⁆ = V := by
    have hi := commutator_isPPerfect_idempotent L (pCoreIn 2 L)
      hL.twoPerfect (isPGroup_pCoreIn 2 L)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    simpa only [pCoreIn, V, U, ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map,
      range_subtype] using hi
  let _ : IsElementaryAbelian 2 V := hL.elementary.map L.subtype
  have hZC : Z ≤ centralizer (L : Set G) := by
    intro z hz l hl
    obtain ⟨x, hx, rfl⟩ := hz
    exact congrArg Subtype.val (mem_center_iff.mp hx.2 ⟨l, hl⟩)
  let D : Subgroup L := W.subgroupOf L ⊔ (ChapterC.blockU L ⊓ center L)
  have hnW : (W.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hLW
  let _ := hnW
  have hDU : D ≤ ChapterC.blockU L := by
    apply sup_le ?_ inf_le_left
    intro x hx
    have hxV : (x : G) ∈ (ChapterC.blockU L).map L.subtype := (show W ≤ V from inf_le_left) hx
    obtain ⟨y, hy, he⟩ := hxV
    exact (Subtype.ext he : y = x) ▸ hy
  rcases hL.irreducible.2 D inferInstance le_sup_right hDU with he | he
  · have hWC : W ≤ centralizer (L : Set G) := by
      intro w hw
      have hd : (⟨w, hWL hw⟩ : L) ∈ D := (show W.subgroupOf L ≤ D from le_sup_left) hw
      rw [he] at hd
      exact hZC (mem_map_of_mem L.subtype hd)
    have hz : ⁅V, L⁆ = ⊥ := hL.twoPerfect.centralizes_of_commuting_fixed
      L Q V hQ hLV hQV hcomm (commutator_eq_bot_iff_le_centralizer.mpr hWC)
    have hVbot : V = ⊥ := hVLcomm.symm.trans hz
    exact False.elim (hL.blockU_ne_bot ((map_injective L.subtype_injective)
      (hVbot.trans (map_bot L.subtype).symm)))
  · have hjoin : W ⊔ Z = V := by
      have hh := congrArg (Subgroup.map L.subtype) he
      simpa only [D, Z, V, U, Subgroup.map_sup, map_subgroupOf_eq_of_le hWL] using hh
    have hWLcomm : ⁅W, L⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hLW
    have hZLcomm : ⁅Z, L⁆ ≤ W := (commutator_eq_bot_iff_le_centralizer.mpr hZC).le.trans bot_le
    have hjoincomm : ⁅W ⊔ Z, L⁆ ≤ W := by
      apply (le_commutatorPreimage_iff (normalizer (W : Set G)) L W (W ⊔ Z) le_rfl).mp
        (sup_le (le_commutatorPreimage W.le_normalizer hWLcomm)
          (le_commutatorPreimage
            ((hZC.trans (centralizer_le hWL)).trans (Subgroup.centralizer_le_normalizer _))
            hZLcomm)) |>.2
    have hVW : V ≤ W := hVLcomm.symm.le.trans (hjoin ▸ hjoincomm)
    exact le_centralizer_iff.mp (hVW.trans inf_le_right)

/-- C.1.11 for the normal single block in the local Baumann calculation. -/
theorem singleBlockCentralizerInput : SingleBlockCentralizerInput (G := G) := by
  intro H R L hH hR hHL hjoin hblock
  have hLH : L ≤ H := hjoin ▸ le_sup_left
  have hRH : R ≤ H := hjoin ▸ le_sup_right
  have hHQ : H ≤ normalizer (pCoreIn 2 H : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHU : H ≤ normalizer (U L : Set G) :=
    hHL.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  apply le_antisymm ?_ (le_inf (pCoreIn_le 2 H)
    (short_core_centralizes hblock.chi.short (isPGroup_pCoreIn 2 H)
      (hLH.trans hHQ) ((pCoreIn_le 2 H).trans hHL)))
  let N := L.subgroupOf H
  let _ : N.Normal := (normal_subgroupOf_iff_le_normalizer hLH).mpr hHL
  have hLchar : HasCharacteristicTwo L :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hLH)).mp
      (normal_core_selfCentralizing hH N)
  have hLC : L ⊓ centralizer (U L : Set G) ≤ pCoreIn 2 L := by
    rintro x ⟨hxL, hxC⟩
    refine mem_map.mpr ⟨⟨x, hxL⟩, intrinsic_centralizer_le_core hLchar ?_, rfl⟩
    intro u hu
    apply Subtype.ext
    exact hxC u (mem_map_of_mem L.subtype hu)
  have hRp : IsPGroup 2 R := by
    obtain ⟨P, hP⟩ := hR
    exact hP ▸ P.isPGroup'.map H.subtype
  have hgen : N ⊔ R.subgroupOf H = ⊤ := by
    apply (map_injective H.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le hRH, ← MonoidHom.range_eq_map, range_subtype]
    exact hjoin
  have hquot : IsPGroup 2 (H ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (R.subgroupOf H) hRp.comap_subtype hgen
  let C := H ⊓ centralizer (U L : Set G)
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨n, hn⟩ := hquot (QuotientGroup.mk' N ⟨c, c.property.1⟩)
    have hcL : (c : G) ^ 2 ^ n ∈ L := by
      have hh : (⟨c, c.property.1⟩ : H) ^ 2 ^ n ∈ N := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' N ((⟨c, c.property.1⟩ : H) ^ 2 ^ n) = 1
        rwa [map_pow]
      exact hh
    have hcCore : (c : G) ^ 2 ^ n ∈ pCoreIn 2 L :=
      hLC ⟨hcL, (centralizer (U L : Set G)).pow_mem c.property.2 _⟩
    obtain ⟨m, hm⟩ := isPGroup_pCoreIn 2 L ⟨_, hcCore⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    change (c : G) ^ 2 ^ (n + m) = 1
    rw [pow_add, pow_mul]
    exact congrArg Subtype.val hm
  apply le_pCoreIn_of_normalizes hCp inf_le_left
  exact (le_inf H.le_normalizer (hHU.trans (normalizer_le_normalizer_centralizer (U L)))).trans
    inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann

end
