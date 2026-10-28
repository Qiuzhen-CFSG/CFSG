module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.CComponent.CharacteristicTwo
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.SylowNormalizerOvergroup
/-!
# Faithful intrinsic Sylow actions on quasisimple local components

In a group of even characteristic, the Sylow centralizer of a normalized
quasisimple local component is trivial. A nontrivial kernel is normalized
by the full Sylow and centralized by the component. Its normalizer has
characteristic two by 1.1.4, as does the component-Sylow join. This contradicts
the presence of a quasisimple component in that join.

The criterion survives solvable odd-order quotient kernels. Restriction to
a containing subnormal component uses the literal Sylow intersection; it
makes no assertion about faithfulness of the original ambient Sylow.
Source: Aschbacher–Smith A.3.12 and C.5.12–13, printed pp.47–48,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]
theorem sylow_centralizer_eq_bot_of_evenCharacteristic
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T) {B : Subgroup G}
    (hB : B ∈ localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥ := by
  let R := (T : Subgroup G) ⊓ centralizer (B : Set G)
  by_contra hne
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (hTB.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf
  have hBR : B ≤ normalizer (R : Set G) :=
    (le_centralizer_iff.mp (show R ≤ centralizer (B : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hR := Chapter1.lemma_1_1_4_2 T hE hne
    (show R ≤ (T : Subgroup G) from inf_le_left)
    ((normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hTR)
  let J := B ⊔ (T : Subgroup G)
  have hJN : J ≤ normalizer (R : Set G) := sup_le hBR hTR
  have hchar : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    have hc := centralizer_pCore_le_of_sylow_le (T.subtype hTR)
      (J.subgroupOf (normalizer (R : Set G)))
      (fun x hx => show (x : G) ∈ J from (show (T : Subgroup G) ≤ J from le_sup_right) hx)
      (Chapter1.mem_He_iff.mp hR.2.2)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe hJN)).mp hc
  let e : B.subgroupOf J ≃* B := subgroupOfEquivOfLe le_sup_left
  let : Nontrivial (B.subgroupOf J) := (nontrivial_iff_ne_bot _).mpr hB.ne_bot
  have hq : IsQuasisimple (B.subgroupOf J) :=
    IsQuasisimple.of_surjective e.symm.toMonoidHom e.symm.surjective
  exact hB.not_isQuasisimple_of_characteristic_two hchar hq

omit [Finite G] in
/-- A central two-subgroup of the smaller group is already in the Sylow kernel. -/
theorem center_eq_bot_of_twoGroup_of_faithful_sylow
    (T : Sylow 2 G) {B : Subgroup G}
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    (hz : IsPGroup 2 (center B)) : center B = ⊥ := by
  let Z := (center B).map B.subtype
  have hZT : Z ≤ (T : Subgroup G) :=
    (hz.map B.subtype).le_sylow_of_normalized T
      (hTB.trans (normalizer_le_normalizer_characteristic_image B (center B)))
  have hZC : Z ≤ centralizer (B : Set G) := by
    rintro _ ⟨z,hz,rfl⟩ b hb
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hb⟩)
  have hZ : Z = ⊥ := bot_unique (hfaith ▸ le_inf hZT hZC)
  exact (map_eq_bot_iff_of_injective (center B) B.subtype_injective).mp hZ

/-- The same kernel criterion passes through a solvable odd-order kernel. -/
theorem sylow_centralizer_eq_bot_of_odd_quotient_evenCharacteristic
    {H : Type*} [Group H] [Finite H] (T : Sylow 2 G)
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (ho : Odd (Nat.card f.ker)) (hE : IsEvenCharacteristic H)
    {B : Subgroup G} (hB : B ∈ localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥ := by
  let S := T.mapSurjective hf
  have hlocal : B.map f ∈ localCComponents S :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB f
  let e : (B.map f).subgroupOf (B.map f ⊔ (S : Subgroup H)) ≃* B.map f :=
    subgroupOfEquivOfLe le_sup_left
  let : Nontrivial ((B.map f).subgroupOf (B.map f ⊔ (S : Subgroup H))) :=
    (nontrivial_iff_ne_bot _).mpr hlocal.ne_bot
  let : Nontrivial (B.map f) := e.symm.surjective.nontrivial
  let : IsQuasisimple (B.map f) :=
    IsQuasisimple.of_surjective (f.subgroupMap B) (f.subgroupMap_surjective B)
  have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S (hE S) hlocal
    ((map_mono hTB).trans (le_normalizer_map f))
  have hdisj : Disjoint (T : Subgroup G) f.ker := by
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact ho.coprime_two_left.pow_left n
  apply bot_unique
  intro x hx
  have hfx : f x ∈ (S : Subgroup H) ⊓ centralizer (B.map f : Set H) := by
    refine ⟨mem_map_of_mem f hx.1, ?_⟩
    rintro y ⟨b,hb,rfl⟩
    simpa only [map_mul] using congrArg f (hx.2 b hb)
  have hk : x ∈ f.ker := by
    change f x = 1
    simpa only [hfaith,mem_bot] using hfx
  exact hdisj.eq_bot.le ⟨hx.1,hk⟩


/-- Restriction keeps the literal Sylow intersection and its normalization. -/
theorem exists_local_sylow_normalizing
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsSubnormal) (hBL : B ≤ L)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L ∧
      B.subgroupOf L ∈ localCComponents S ∧
      (S : Subgroup L) ≤ normalizer (B.subgroupOf L : Set L) := by
  obtain ⟨S,hS,hlocal⟩ := exists_local_sylow_restriction T hB hBL hL
  refine ⟨S,hS,hlocal,?_⟩
  rw [hS, ← subgroupOf_normalizer_eq hBL]
  exact comap_mono hTB

omit [Finite G] in
/-- The smaller group's quasisimplicity survives the actual inclusion coordinates. -/
theorem quasisimple_subgroupOf {B L : Subgroup G} (hBL : B ≤ L)
    [IsQuasisimple B] : IsQuasisimple (B.subgroupOf L) := by
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  let e := subgroupOfEquivOfLe hBL
  let : Nontrivial (B.subgroupOf L) := e.surjective.nontrivial
  exact IsQuasisimple.of_surjective e.symm.toMonoidHom e.symm.surjective

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
