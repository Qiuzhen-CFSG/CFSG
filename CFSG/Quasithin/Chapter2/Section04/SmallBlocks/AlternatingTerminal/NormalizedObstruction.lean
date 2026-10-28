module

public import Theory.GroupTheory.CharacteristicPGroupExtension
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.Persistence
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction

/-!
# A normalized local obstruction to paired alternating-five blocks

A characteristic-two subgroup normalized by the original half-Sylow group
has a characteristic-two join with that actor. Original-source persistence
then makes the block local at a full Sylow of the join. Restriction to the
normal subgroup supplies its own full-Sylow local component, contradicting
an intrinsic model obstruction. No larger ambient Sylow is substituted.

Source: Aschbacher–Smith 2.4.25, printed p.543, the final starred-persistence
argument. Model obstruction producers are connected separately.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem he_sup_of_normalized_two {N R : Subgroup G}
    (hN : N ∈ Chapter1.He G) (hR : IsPGroup 2 R)
    (hRN : R ≤ normalizer (N : Set G)) : N ⊔ R ∈ Chapter1.He G := by
  let X := N ⊔ R
  let A := N.subgroupOf X
  let B := R.subgroupOf X
  have hNX : N ≤ X := le_sup_left
  have hRX : R ≤ X := le_sup_right
  let e : A ≃* N := subgroupOfEquivOfLe hNX
  have hn : A.Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr
    (sup_le N.le_normalizer hRN)
  let := hn
  have hA : centralizer (pCore 2 A : Set A) ≤ pCore 2 A :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr (Chapter1.mem_He_iff.mp hN)
  have hB : IsPGroup 2 B := hR.comap_subtype
  have hgen : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup hNX hRX]
    exact subgroupOf_self _
  let q := QuotientGroup.mk' A
  have hmap : B.map q = ⊤ := by
    have hh := congrArg (Subgroup.map q) hgen
    rw [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,map_top_of_surjective _
      (QuotientGroup.mk'_surjective A)] at hh
    exact hh
  have hQ : IsPGroup 2 (X ⧸ A) := by
    have ht : IsPGroup 2 (⊤ : Subgroup (X ⧸ A)) := hmap ▸ hB.map q
    exact ht.of_surjective (topEquiv (G := X ⧸ A)).toMonoidHom
      (topEquiv (G := X ⧸ A)).surjective
  exact Chapter1.mem_He_iff.mpr
    (centralizer_pCore_le_of_normal_pGroup_quotient 2 A hA hQ)

variable {M : Subgroup G}

theorem MinimalBlockSetup.alternating_no_normalized_local_obstruction
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    {R N : Subgroup G}
    (hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hi : R.relIndex ((d.S : Subgroup d.H).map d.H.subtype) = 2)
    (hR : R ∈ beta M)
    (hL : d.block.map d.H.subtype ∈ Chapter1.L G R)
    (hN : N ∈ Chapter1.He G) (hLN : d.block.map d.H.subtype ≤ N)
    (hRN : R ≤ normalizer (N : Set G))
    (hbad : ∀ Q : Sylow 2 N,
      (d.block.map d.H.subtype).subgroupOf N ∉ ChapterA.Section03.localCComponents Q) :
    False := by
  let L := d.block.map d.H.subtype
  let X := N ⊔ R
  have hNX : N ≤ X := le_sup_left
  have hRX : R ≤ X := le_sup_right
  have hLX : L ≤ X := hLN.trans hNX
  have hRp : IsPGroup 2 R := (d.S.isPGroup'.map d.H.subtype).to_le hRS
  have hX : X ∈ Chapter1.He G := he_sup_of_normalized_two hN hRp hRN
  obtain ⟨P,hRP⟩ := (hRp.comap_subtype (K := X)).exists_le_sylow
  have hRPa : R ≤ (P : Subgroup X).map X.subtype := by
    intro r hr
    exact ⟨⟨r,hRX hr⟩,hRP hr,rfl⟩
  have hloc := d.alternating_persistence_overgroup hG T hTM hu hRS hi hR hL hX hLX P hRPa
  have hlocX : L.subgroupOf X ∈ ChapterA.Section03.localCComponents P := by
    have hh := ChapterA.Section03.SourceEmbeddings.local_restrict hloc hLX
    simpa only [subgroupOf,comap_map_eq_self_of_injective X.subtype_injective] using hh
  have hn : (N.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr
    (sup_le N.le_normalizer hRN)
  obtain ⟨Q,_,hlocN⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction P
    hlocX (show L.subgroupOf X ≤ N.subgroupOf X from comap_mono hLN) hn.isSubnormal
  let e : N.subgroupOf X ≃* N := subgroupOfEquivOfLe hNX
  have hes : Function.Surjective e.toMonoidHom := e.surjective
  let QN : Sylow 2 N := Q.mapSurjective (f := e.toMonoidHom) hes
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocN e.toMonoidHom
  have he : ((L.subgroupOf X).subgroupOf (N.subgroupOf X)).map e.toMonoidHom =
      L.subgroupOf N := by
    ext n
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hnL
      exact ⟨⟨⟨n.val,hNX n.property⟩,n.property⟩,hnL,rfl⟩
  apply hbad QN
  change L.subgroupOf N ∈ ChapterA.Section03.localCComponents
    (Q.mapSurjective (f := e.toMonoidHom) hes : Subgroup N)
  rw [Sylow.coe_mapSurjective]
  exact he ▸ hm
end CFSG.Quasithin.Chapter2
