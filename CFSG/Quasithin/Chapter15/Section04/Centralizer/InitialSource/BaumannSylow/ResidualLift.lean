module
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Sylow
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# Lifting Baumann's conclusion through the actual action

If the kernel of an action is a two-group and the two-residual has a
three-group image, its two-core lies in the Sylow centralizer and has odd
index in the residual.  The genuine alpha decomposition of B.2.18 then
puts that core in the Baumann subgroup, which is consequently Sylow in
its join with the residual.

This is the final lifting step of Aschbacher--Smith B.6.10, printed p.117,
used with the one-plane and two-plane actions in 15.4.11.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
open ChapterB ChapterB.BaumannArgument
variable {G A : Type*} [Group G] [Finite G] [Group A]

omit [Finite G] in
theorem residual_core_le_kernel (f : G →* A)
    (hL : IsPGroup 3 ((pResidual 2 G).map f)) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ f.ker := by
  let C := (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype
  have hCp : IsPGroup 2 (C.map f) := (pCore_isPGroup.map _).map f
  have hCl : C.map f ≤ (pResidual 2 G).map f := map_mono (map_subtype_le _)
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (C.map f)
    ((pResidual 2 G).map f) hCp hL
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp
    ((le_inf le_rfl hCl).trans (disjoint_iff.mp hd).le))

theorem residual_core_odd_index (f : G →* A) (hk : IsPGroup 2 f.ker)
    (hL : IsPGroup 3 ((pResidual 2 G).map f)) :
    ¬ 2 ∣ (pCore 2 (pResidual 2 G)).index := by
  let L := pResidual 2 G
  let q := f.comp L.subtype
  have hqr : q.range = L.map f := by rw [MonoidHom.range_comp, range_subtype]
  have hp : IsPGroup 3 q.range := hqr.symm ▸ hL
  have hquot : IsPGroup 3 (L ⧸ q.ker) :=
    hp.of_equiv (QuotientGroup.quotientKerEquivRange q).symm
  have hqk : IsPGroup 2 q.ker := hk.comap_subtype
  have hkle : q.ker ≤ pCore 2 L := le_sSup ⟨inferInstance,hqk⟩
  obtain ⟨n,hn⟩ := hquot.exists_card_eq
  have hodd : ¬ 2 ∣ q.ker.index := by
    change ¬ 2 ∣ Nat.card (L ⧸ q.ker)
    rw [hn]
    exact (Nat.Prime.dvd_of_dvd_pow Nat.prime_two ·) |>.mt (by decide)
  exact fun h => hodd (h.trans (index_dvd_of_le hkle))

/-- The original alpha decomposition, with the original action kernel,
gives the requested Sylow witness; no Sylow conclusion is an input. -/
theorem sylow_of_alpha (R : Sylow 2 G) (W : Subgroup G)
    (f : G →* A) (hk : IsPGroup 2 f.ker)
    (hker : f.ker = centralizer (W : Set G))
    (hL : IsPGroup 3 ((pResidual 2 G).map f))
    (ha : thompsonAlpha (R : Subgroup G) =
      (thompsonAlpha (R : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (W ⊓ centralizer (elementaryAbelianMaxJ (R : Subgroup G) : Set G))) :
    Chapter1.IsSylowIn 2 (baumann (R : Subgroup G))
      (pResidual 2 G ⊔ baumann (R : Subgroup G)) := by
  have hcore := residual_core_le_kernel f hL
  have hloc : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤
      (R : Subgroup G) ⊓ centralizer (W : Set G) :=
    le_inf (hcore.trans (hk.le_sylow_of_normal R)) (hcore.trans_eq hker)
  have hba := core_le_baumann_of_decomposition W (R : Subgroup G)
    (pResidual 2 G) hloc ha
  exact IsPGroup.exists_sylow_sup_of_coprime_index (pResidual 2 G)
    (baumann (R : Subgroup G)) (R.isPGroup'.to_le inf_le_left)
    le_normalizer_of_normal (pCore 2 (pResidual 2 G))
    (residual_core_odd_index f hk hL) hba

end CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
