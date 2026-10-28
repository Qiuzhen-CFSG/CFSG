module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.Bounds
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The root-center obstruction to E-generation

Let L be a simple subgroup and S its intersection with a specified ambient
Sylow two-subgroup. Use the ambient conjugates of Z(S) as the elementary
family. If Z(S) is the unique such conjugate contained in T, its weak closure
is Z(S), whose normalizer is proper. E0 forces every applicable E-member to
contain S. A root-overgroup alternative then either traps it in that normalizer
or forces it to contain L. In the latter case both literal E-member quotients
preserve the rank of Z(S), since their kernels are solvable.

The subgroup, center and conjugacy family are actual embedded subgroups.
The final theorem is conditional on the geometric model calculations; it does
not assert that PSU₃ supplies them. These calculations are independent of the
quotient-rank argument and must be discharged in the source assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, E.1.1–6
and E.1.14(1), printed pp.209–211, 214 (citing Aschbacher 1982, Lemma 4.7).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSU3
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- The defining-characteristic subgroup inside the specified ambient Sylow group. -/
def rootSection (L : Subgroup G) (T : Sylow 2 G) : Subgroup G := L ⊓ T

/-- The center of the intrinsic root subgroup, embedded back in the ambient group. -/
def rootCenter (L : Subgroup G) (T : Sylow 2 G) : Subgroup G :=
  (center (rootSection L T)).map (rootSection L T).subtype

/-- The actual ambient conjugacy class used as the elementary family. -/
def centerFamily (Z : Subgroup G) : Set (Subgroup G) :=
  {A | ∃ g : G, Z.map (MulAut.conj g).toMonoidHom = A}

private theorem rank_image_of_simple {L A K : Subgroup G} [IsSimpleGroup L]
    (hns : ¬ Group.IsSolvable L) (hAL : A ≤ L) (hLK : L ≤ K)
    (N : Subgroup K) [N.Normal] [Group.IsSolvable N] :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) = Group.rank A := by
  let j := inclusion hLK
  let q := QuotientGroup.mk' N
  let f := q.comp j
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with h | h
    · exact h
    · have hjN (x : L) : j x ∈ N := by
        apply (QuotientGroup.eq_one_iff _).mp
        exact (show x ∈ f.ker from h ▸ mem_top x)
      let jN : L →* N := j.codRestrict N hjN
      have hinj : Function.Injective jN := by
        intro x y hxy
        exact Subtype.ext (congrArg (fun z : N => ((z : K) : G)) hxy)
      exact (hns (Group.isSolvable_of_isSolvable_injective hinj)).elim
  let a := A.subgroupOf K
  let qa := q.subgroupMap a
  have hqa : Function.Injective qa := by
    intro x y hxy
    have hfx : f ⟨((x : K) : G), hAL x.property⟩ =
        f ⟨((y : K) : G), hAL y.property⟩ := congrArg Subtype.val hxy
    have he := congrArg Subtype.val (hf hfx)
    exact Subtype.ext (Subtype.ext he)
  calc
    _ = Group.rank a := (Group.rank_congr (MulEquiv.ofBijective qa
      ⟨hqa, q.subgroupMap_surjective a⟩)).symm
    _ = Group.rank A := Group.rank_congr (subgroupOfEquivOfLe (hAL.trans hLK))

/-- Solvable kernels in both literal E-member quotients preserve the rank of
an elementary subgroup of a nonsolvable simple subgroup contained in K. -/
theorem rank_le_of_simple_le_member {L T A K : Subgroup G} [IsSimpleGroup L]
    (hns : ¬ Group.IsSolvable L) (hAL : A ≤ L) (hLK : L ≤ K)
    {i : ℕ} (hK : IsEMemberAt i T A K) : Group.rank A ≤ i := by
  rcases hK.2 with h | h
  · let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
    exact (rank_image_of_simple hns hAL hLK (pCore 2 K)) ▸ h.2
  · exact (rank_image_of_simple hns hAL hLK (solvableRadical K)) ▸ h.2

omit [Finite G] in
/-- The center of the inner root subgroup is centralized by that whole subgroup,
so E0 forces every E-member for it to contain the root subgroup. -/
theorem rootSection_le_tau (L : Subgroup G) (T : Sylow 2 G) :
    rootSection L T ≤ tau (T : Subgroup G) (rootCenter L T) := by
  intro x hx
  apply mem_centralizerModulo_iff.mpr
  refine ⟨hx.2, ?_⟩
  rintro z ⟨z, hz, rfl⟩
  have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩)
  change x * (z : G) = (z : G) * x at hc
  change ⁅(z : G), x⁆ ∈ pCore 2 G
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc.symm]
  exact one_mem _

omit [Finite G] in
/-- The center conjugacy class is a genuine elementary family. -/
theorem centerFamily_elementary (Z : Subgroup G) [IsElementaryAbelian 2 Z] :
    IsElementaryFamily (centerFamily Z) := by
  constructor
  · rintro A ⟨g, rfl⟩
    exact IsElementaryAbelian.map _
  · rintro g A ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    rw [map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
/-- Uniqueness of the inner center in T computes the weak closure exactly. -/
theorem weakClosure_centerFamily (T : Sylow 2 G) (Z : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G))
    (huniq : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      Z.map (MulAut.conj g).toMonoidHom = Z) :
    weakClosure (T : Subgroup G) (centerFamily Z) = Z := by
  apply le_antisymm
  · apply sSup_le
    rintro A ⟨⟨g, rfl⟩, hAT⟩
    exact (huniq g hAT).le
  · apply le_sSup
    exact ⟨⟨1, by ext x; simp [mem_map]⟩, hZT⟩

omit [Finite G] in
/-- A simple subgroup does not normalize any proper nontrivial subgroup of itself. -/
theorem not_le_normalizer (L Z : Subgroup G) [IsSimpleGroup L]
    (hZL : Z ≤ L) (hZ0 : Z ≠ ⊥) (hZLne : Z ≠ L) :
    ¬ L ≤ normalizer (Z : Set G) := by
  intro h
  let : (Z.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hZL).mpr h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Z.subgroupOf L) inferInstance with h | h
  · apply hZ0
    have hh := congrArg (fun U : Subgroup L => U.map L.subtype) h
    simpa [subgroupOf_map_subtype, inf_eq_left.mpr hZL, ← MonoidHom.range_eq_map, range_subtype] using hh
  · apply hZLne
    have hh := congrArg (fun U : Subgroup L => U.map L.subtype) h
    simpa [subgroupOf_map_subtype, inf_eq_left.mpr hZL, ← MonoidHom.range_eq_map, range_subtype] using hh

omit [Finite G] in
/-- In particular the ambient normalizer is proper. -/
theorem normalizer_ne_top (L Z : Subgroup G) [IsSimpleGroup L]
    (hZL : Z ≤ L) (hZ0 : Z ≠ ⊥) (hZLne : Z ≠ L) :
    normalizer (Z : Set G) ≠ ⊤ := by
  intro h
  exact not_le_normalizer L Z hZL hZ0 hZLne (h ▸ le_top)

omit [Finite G] in
/-- A proper nontrivial subgroup also excludes the solvable simple case. -/
theorem not_solvable_of_proper_subgroup (L Z : Subgroup G) [IsSimpleGroup L]
    (hZL : Z ≤ L) (hZ0 : Z ≠ ⊥) (hZLne : Z ≠ L) :
    ¬ Group.IsSolvable L := by
  intro hs
  have hc := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  apply not_le_normalizer L Z hZL hZ0 hZLne
  apply le_trans _ (centralizer_le_normalizer _)
  intro x hx
  apply mem_centralizer_iff.mpr
  intro z hz
  exact congrArg Subtype.val (hc ⟨z, hZL hz⟩ ⟨x, hx⟩)

omit [Finite G] in
/-- Two distinct conjugate root groups generating L give the overgroup
alternative, for arbitrary ambient conjugation, including outer automorphisms. -/
theorem root_overgroup_of_conjugate_join (L : Subgroup G) (T : Sylow 2 G)
    (hpair : ∀ g : G, (rootSection L T).map (MulAut.conj g).toMonoidHom ≠
      rootSection L T →
      L ≤ rootSection L T ⊔ (rootSection L T).map (MulAut.conj g).toMonoidHom)
    (K : Subgroup G) (hSK : rootSection L T ≤ K)
    (hKN : ¬ K ≤ normalizer (rootCenter L T : Set G)) : L ≤ K := by
  obtain ⟨g, hgK, hgN⟩ := SetLike.not_le_iff_exists.mp hKN
  have hne : (rootSection L T).map (MulAut.conj g).toMonoidHom ≠
      rootSection L T := by
    intro heq
    apply hgN
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ((center (rootSection L T)).map (rootSection L T).subtype).map
      (MulAut.conj g).toMonoidHom = _
    rw [map_embeddedCenter _ _ (MulAut.conj g).injective, heq]
    rfl
  apply (hpair g hne).trans
  apply sup_le hSK
  rintro x ⟨s, hs, rfl⟩
  exact K.mul_mem (K.mul_mem hgK (hSK hs)) (K.inv_mem hgK)

/-- Conditional lower-bound assembly. The two geometric model calculations are
uniqueness of the root center inside T, and the root-overgroup alternative.
No E-generation failure or quotient-rank conclusion is assumed. -/
theorem not_isEGenerated_of_root_geometry (L : Subgroup G) (T : Sylow 2 G)
    [IsSimpleGroup L] {f : ℕ} (hf : 0 < f)
    (hZelem : IsElementaryAbelian 2 (rootCenter L T))
    (hZ0 : rootCenter L T ≠ ⊥) (hZLne : rootCenter L T ≠ L)
    (hZrank : Group.rank (rootCenter L T) = f)
    (huniq : ∀ g : G, (rootCenter L T).map (MulAut.conj g).toMonoidHom ≤
      (T : Subgroup G) →
      (rootCenter L T).map (MulAut.conj g).toMonoidHom = rootCenter L T)
    (hover : ∀ K : Subgroup G, rootSection L T ≤ K →
      ¬ K ≤ normalizer (rootCenter L T : Set G) → L ≤ K) :
    ¬ IsEGenerated (f - 1) G := by
  let Z := rootCenter L T
  let : IsElementaryAbelian 2 Z := hZelem
  have hZL : Z ≤ L := (map_subtype_le _).trans inf_le_left
  have hZT : Z ≤ (T : Subgroup G) := (map_subtype_le _).trans inf_le_right
  apply not_isEGenerated_of_members_le T (centerFamily Z) (centerFamily_elementary Z)
    (normalizer (Z : Set G)) (normalizer_ne_top L Z hZL hZ0 hZLne)
  · rw [weakClosure_centerFamily T Z hZT huniq]
  · rintro A ⟨g, rfl⟩ hAT K hK
    have heq := huniq g hAT
    rw [heq] at hK
    by_contra hKM
    have hSK : rootSection L T ≤ K :=
      (rootSection_le_tau L T).trans (hK.1.2.2.2.1.trans inf_le_right)
    have hns := not_solvable_of_proper_subgroup L Z hZL hZ0 hZLne
    have hr := rank_le_of_simple_le_member hns hZL (hover K hSK hKM) hK
    rw [hZrank] at hr
    omega

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSU3
