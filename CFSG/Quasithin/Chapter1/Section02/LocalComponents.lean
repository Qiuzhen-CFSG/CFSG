module

public import CFSG.Quasithin.Chapter1.Defs
public import CFSG.Quasithin.ChapterA.Section03.Basic
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore

/-!
# The Chapter 1 local C-component families

Definition 1.2.3 requires all three conditions: `B` is a C-component of
`⟨B,S⟩`, `S` is Sylow two there, and that join has nontrivial two-core.
`LStar` takes inclusion-maximal members. `LIn` and `LStarIn` express the
intrinsic families of an overgroup in a common ambient group; the transport
lemmas identify these with the original definitions, when `S ≤ H`.

For Lemma 1.2.6, restrict a C-component and the Sylow subgroup to their
join. The normal two-core of `H` is contained in `S`, hence in that join,
and its restriction lies in the join's two-core. This elementary argument
does not use quasithinness or characteristic two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Definition 1.2.3 and Lemma 1.2.6, pp. 505–506.
The quotient classification deductions are separate from these definitions.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1
variable {G G' : Type*} [Group G] [Group G']

/-- A Sylow subgroup of `H`, represented as a subgroup of the ambient group. -/
def IsSylowIn (p : ℕ) (S H : Subgroup G) : Prop :=
  ∃ P : Sylow p H, (P : Subgroup H).map H.subtype = S

/-- The Sylow witness is equivalent to maximality among the p-subgroups of `H`. -/
theorem isSylowIn_iff {p : ℕ} {S H : Subgroup G} :
    IsSylowIn p S H ↔ IsPGroup p S ∧ S ≤ H ∧
      ∀ U : Subgroup G, IsPGroup p U → S ≤ U → U ≤ H → U = S := by
  constructor
  · rintro ⟨P, rfl⟩
    refine ⟨P.isPGroup'.map _, map_subtype_le _, ?_⟩
    intro U hU hPU hUH
    have he : U.subgroupOf H = (P : Subgroup H) :=
      P.is_maximal' hU.comap_subtype (by
        intro x hx
        exact hPU (mem_map.mpr ⟨x, hx, rfl⟩))
    simpa only [map_subgroupOf_eq_of_le hUH] using congrArg (map H.subtype) he
  · rintro ⟨hp, hSH, hmax⟩
    obtain ⟨P, hP⟩ := (hp.comap_subtype : IsPGroup p (S.subgroupOf H)).exists_le_sylow
    refine ⟨P, hmax _ (P.isPGroup'.map _) ?_ (map_subtype_le _)⟩
    calc
      S = (S.subgroupOf H).map H.subtype := (map_subgroupOf_eq_of_le hSH).symm
      _ ≤ (P : Subgroup H).map H.subtype := map_mono hP

/-- A Sylow subgroup remains Sylow in any intermediate overgroup. -/
theorem IsSylowIn.restrict {p : ℕ} {S H K : Subgroup G}
    (h : IsSylowIn p S H) (hSK : S ≤ K) (hKH : K ≤ H) : IsSylowIn p S K := by
  obtain ⟨hp, _, hm⟩ := isSylowIn_iff.mp h
  exact isSylowIn_iff.mpr ⟨hp, hSK, fun U hU hSU hUK => hm U hU hSU (hUK.trans hKH)⟩

/-- Faithful embeddings preserve and reflect relative Sylow membership. -/
theorem IsSylowIn.map_iff {p : ℕ} {S H : Subgroup G}
    (f : G →* G') (hf : Function.Injective f) :
    IsSylowIn p (S.map f) (H.map f) ↔ IsSylowIn p S H := by
  simp only [isSylowIn_iff]
  constructor
  · rintro ⟨hp, hle, hm⟩
    refine ⟨hp.of_equiv (S.equivMapOfInjective f hf).symm,
      (map_le_map_iff_of_injective hf).mp hle, ?_⟩
    intro U hU hSU hUH
    exact (map_injective hf) (hm (U.map f) (hU.map f) (map_mono hSU) (map_mono hUH))
  · rintro ⟨hp, hle, hm⟩
    refine ⟨hp.map f, map_mono hle, ?_⟩
    intro U hU hSU hUH
    have he : U.comap f = S := hm _ (hU.comap_of_injective f hf)
      (map_le_iff_le_comap.mp hSU) (by
        simpa only [comap_map_eq_self_of_injective hf] using comap_mono (f := f) hUH)
    rw [← he, map_comap_eq_self]
    exact hUH.trans (map_le_range f H)

/-- Definition 1.2.3, retaining C-component, Sylow, and nontrivial two-core conditions. -/
def L (G : Type*) [Group G] (S : Subgroup G) : Set (Subgroup G) :=
  {B | (B.subgroupOf (B ⊔ S)).IsCComponent ∧
    IsSylowIn 2 S (B ⊔ S) ∧ (B ⊔ S).pCoreIn 2 ≠ ⊥}

/-- The inclusion-maximal members of the family in Definition 1.2.3. -/
def LStar (G : Type*) [Group G] (S : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ L G S ∧ ∀ D ∈ L G S, B ≤ D → D = B}

/-- The members of `L(G,S)` contained in `H`; use with `S ≤ H` for `L(H,S)`. -/
def LIn (H S : Subgroup G) : Set (Subgroup G) := {B | B ≤ H ∧ B ∈ L G S}

/-- Maximality within the ambient realization of `L(H,S)`, not within `L(G,S)`. -/
def LStarIn (H S : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ LIn H S ∧ ∀ D ∈ LIn H S, B ≤ D → D = B}

/-- The C-components of `H`, represented in the ambient group. -/
def cComponentsIn (H : Subgroup G) : Set (Subgroup G) :=
  {B | B ≤ H ∧ (B.subgroupOf H).IsCComponent}

private theorem map_subgroupOf_equiv {B H : Subgroup G} (hBH : B ≤ H)
    (f : G →* G') (hf : Function.Injective f) :
    (B.subgroupOf H).map (H.equivMapOfInjective f hf).toMonoidHom =
      (B.map f).subgroupOf (H.map f) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_map.mpr ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨⟨y, hBH hy⟩, hy, Subtype.ext he⟩

private theorem isCComponent_map_equiv_iff {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (D : Subgroup A) :
    (D.map e.toMonoidHom).IsCComponent ↔ D.IsCComponent := by
  constructor
  · intro h
    simpa [map_map] using h.map_equiv e.symm
  · exact fun h => h.map_equiv e

/-- Faithful embeddings preserve the whole local-family definition. -/
theorem mem_L_map_iff (f : G →* G') (hf : Function.Injective f) {B S : Subgroup G} :
    B.map f ∈ L G' (S.map f) ↔ B ∈ L G S := by
  unfold L
  change ((B.map f).subgroupOf (B.map f ⊔ S.map f)).IsCComponent ∧
    IsSylowIn 2 (S.map f) (B.map f ⊔ S.map f) ∧ (B.map f ⊔ S.map f).pCoreIn 2 ≠ ⊥ ↔ _
  rw [← Subgroup.map_sup, IsSylowIn.map_iff f hf,
    ← map_subgroupOf_equiv le_sup_left f hf, isCComponent_map_equiv_iff,
    ← map_pCoreIn_of_injective 2 (B ⊔ S) f hf]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    not_congr (((B ⊔ S).pCoreIn 2).map_eq_bot_iff_of_injective hf)

/-- The ambient realization agrees with the intrinsic family of `H`. -/
theorem mem_LIn_iff_subgroupOf {H S B : Subgroup G} (hSH : S ≤ H) (hBH : B ≤ H) :
    B ∈ LIn H S ↔ B.subgroupOf H ∈ L H (S.subgroupOf H) := by
  rw [← mem_L_map_iff H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hSH, map_subgroupOf_eq_of_le hBH]
  exact and_iff_right hBH

/-- The second inclusion in Lemma 1.2.6. -/
theorem LIn_subset {H S : Subgroup G} : LIn H S ⊆ L G S := fun _ h => h.2

/-- Enlarging the allowed ambient overgroup enlarges its local family. -/
theorem LIn_mono {H K S : Subgroup G} (hHK : H ≤ K) : LIn H S ⊆ LIn K S :=
  fun _ h => ⟨h.1.trans hHK, h.2⟩

/-- Transport of maximality in the intrinsic family of `H`. -/
theorem mem_LStarIn_iff_subgroupOf {H S B : Subgroup G} (hSH : S ≤ H) (hBH : B ≤ H) :
    B ∈ LStarIn H S ↔ B.subgroupOf H ∈ LStar H (S.subgroupOf H) := by
  constructor
  · rintro ⟨hB, hm⟩
    refine ⟨(mem_LIn_iff_subgroupOf hSH hBH).mp hB, ?_⟩
    intro D hD hBD
    have hDm : D.map H.subtype ∈ LIn H S := by
      refine ⟨map_subtype_le _, ?_⟩
      simpa only [map_subgroupOf_eq_of_le hSH] using
        (mem_L_map_iff H.subtype H.subtype_injective).mpr hD
    have he := hm _ hDm (by
      simpa only [map_subgroupOf_eq_of_le hBH] using map_mono (f := H.subtype) hBD)
    apply map_injective H.subtype_injective
    simpa only [map_subgroupOf_eq_of_le hBH] using he
  · rintro ⟨hB, hm⟩
    refine ⟨(mem_LIn_iff_subgroupOf hSH hBH).mpr hB, ?_⟩
    intro D hD hBD
    have he := hm (D.subgroupOf H) ((mem_LIn_iff_subgroupOf hSH hD.1).mp hD)
      (comap_mono hBD)
    simpa only [map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hD.1] using
      congrArg (map H.subtype) he

/-- Isomorphisms preserve and reflect maximal local components. -/
theorem mem_LStar_map_iff (e : G ≃* G') {B S : Subgroup G} :
    B.map e.toMonoidHom ∈ LStar G' (S.map e.toMonoidHom) ↔ B ∈ LStar G S := by
  constructor
  · rintro ⟨hB, hm⟩
    refine ⟨(mem_L_map_iff e.toMonoidHom e.injective).mp hB, ?_⟩
    intro D hD hBD
    exact map_injective e.injective (hm _
      ((mem_L_map_iff e.toMonoidHom e.injective).mpr hD) (map_mono hBD))
  · rintro ⟨hB, hm⟩
    refine ⟨(mem_L_map_iff e.toMonoidHom e.injective).mpr hB, ?_⟩
    intro D hD hBD
    have hd : D.map e.symm.toMonoidHom ∈ L G S := by
      simpa [map_map] using (mem_L_map_iff e.symm.toMonoidHom e.symm.injective).mpr hD
    have hle : B ≤ D.map e.symm.toMonoidHom := by
      simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hBD
    have he := congrArg (map e.toMonoidHom) (hm _ hd hle)
    simpa [map_map] using he

/-- Every local component in a finite group lies in a maximal one. -/
theorem exists_mem_LStar_ge [Finite G] {S B : Subgroup G} (hB : B ∈ L G S) :
    ∃ D ∈ LStar G S, B ≤ D := by
  obtain ⟨D, hBD, hD, hm⟩ := Finite.exists_le_maximal hB
  exact ⟨D, ⟨hD, fun E hE hDE => le_antisymm (hm hE hDE) hDE⟩, hBD⟩

/-- Every member of the local family is perfect. -/
theorem mem_L_isPerfect {S B : Subgroup G} (hB : B ∈ L G S) : Group.IsPerfect B := by
  let := hB.1.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

/-- Every member of the local family is nonsolvable. -/
theorem mem_L_not_isSolvable {S B : Subgroup G} (hB : B ∈ L G S) :
    ¬ Group.IsSolvable B := by
  intro hs
  let := hs
  exact hB.1.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).injective)

/-- A C-component of a group with nontrivial two-core belongs to its Sylow local family. -/
theorem mem_L_of_cComponent {H B S : Subgroup G} (hH : H ∈ Chapter1.H G)
    (hS : IsSylowIn 2 S H) (hBH : B ≤ H) (hB : (B.subgroupOf H).IsCComponent) :
    B ∈ L G S := by
  obtain ⟨P, hP⟩ := hS
  have hSH : S ≤ H := hP ▸ map_subtype_le (P : Subgroup H)
  have hjoin : B ⊔ S ≤ H := sup_le hBH hSH
  have hcore : H.pCoreIn 2 ≤ (B ⊔ S).pCoreIn 2 := by
    have hcoreS : H.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow H P
    have hcoreJ : H.pCoreIn 2 ≤ B ⊔ S := hcoreS.trans le_sup_right
    exact (le_inf hcoreJ le_rfl).trans (inf_pCoreIn_le_of_le 2 hjoin)
  exact ⟨hB.subgroupOf_of_le le_sup_left hjoin,
    (IsSylowIn.restrict ⟨P, hP⟩ le_sup_right hjoin),
    fun he => hH (bot_unique (he ▸ hcore))⟩

/-- Lemma 1.2.6: `C(H) ⊆ L(H,T) ⊆ L(G,T)` for `H ∈ H(T)`. -/
theorem lemma_1_2_6 (T : Sylow 2 G) {H : Subgroup G}
    (hH : H ∈ HOver G (T : Set G)) :
    cComponentsIn H ⊆ LIn H (T : Subgroup G) ∧ LIn H (T : Subgroup G) ⊆ L G T := by
  have hTH : (T : Subgroup G) ≤ H := hH.2
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
  exact ⟨fun B hB => ⟨hB.1, mem_L_of_cComponent hH.1 hSyl hB.1 hB.2⟩, LIn_subset⟩
/-- Unique containing C-components transport between intrinsic and ambient subgroup notation. -/
theorem existsUnique_cComponentsIn_iff {H B : Subgroup G} (hBH : B ≤ H) :
    (∃! K : Subgroup H, K.IsCComponent ∧ B.subgroupOf H ≤ K) ↔
      ∃! K : Subgroup G, K ∈ cComponentsIn H ∧ B ≤ K := by
  constructor
  · rintro ⟨K, ⟨hK, hBK⟩, hu⟩
    have hm : (K.map H.subtype).subgroupOf H = K :=
      comap_map_eq_self_of_injective H.subtype_injective _
    refine ⟨K.map H.subtype, ⟨⟨map_subtype_le _, hm.symm ▸ hK⟩, ?_⟩, ?_⟩
    · simpa only [map_subgroupOf_eq_of_le hBH] using map_mono (f := H.subtype) hBK
    · intro D hD
      have he := hu (D.subgroupOf H) ⟨hD.1.2, comap_mono hD.2⟩
      simpa only [map_subgroupOf_eq_of_le hD.1.1] using congrArg (map H.subtype) he
  · rintro ⟨K, ⟨hK, hBK⟩, hu⟩
    refine ⟨K.subgroupOf H, ⟨hK.2, comap_mono hBK⟩, ?_⟩
    intro D hD
    have hm : (D.map H.subtype).subgroupOf H = D :=
      comap_map_eq_self_of_injective H.subtype_injective _
    have he := hu (D.map H.subtype) ⟨⟨map_subtype_le _, hm.symm ▸ hD.1⟩, by
      simpa only [map_subgroupOf_eq_of_le hBH] using map_mono (f := H.subtype) hD.2⟩
    simpa only [hm] using congrArg (fun A : Subgroup G => A.subgroupOf H) he

end CFSG.Quasithin.Chapter1
