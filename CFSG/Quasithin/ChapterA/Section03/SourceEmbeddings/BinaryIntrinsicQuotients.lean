module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Intrinsic quotients of binary local C-components

Every local C-component B of GL_n(2), n ≤ 5, has B/O₂(B) isomorphic
to GL_m(2) for 3 ≤ m ≤ n. A proper Sylow overgroup is a partial-flag
stabilizer. Pass through its actual two-block Levi map, discard the
solvable factor using perfection, and induct on the remaining dimension.
The kernel on B is a two-group, so its intrinsic two-core quotient is
preserved. The final application retains the original inclusion B≤K and
the full Sylow intersection when K itself is only a local component.

This is the binary containing-component calculation used by the Chapter 12
LocalConfigurationRigidityHigherBinaryCatalogue extension.
Source: Aschbacher–Smith, A.3.12(4–5), printed pp.47–48, and the containing
chain in original 12.2.25, printed p.805. Imported matrix and exceptional
isomorphism facts retain the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
open BinaryLinear.InvariantNodeActions
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem small_solvable (n : ℕ) (hn : n ≤ 2) : Group.IsSolvable (LinearGroup n) := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  have hc : Nat.card (LinearGroup n) = ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
    simp
  rw [hc] at hd
  interval_cases n
  · norm_num at hd
    exact (hp.ne_one hd).elim
  · norm_num at hd
    exact (hp.ne_one hd).elim
  · norm_num [Fin.prod_univ_two] at hd
    have hh := hp.dvd_mul.mp (show p ∣ 2*3 from hd)
    exact hh.elim
      (fun h => Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
      (fun h => Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one))

private theorem perfect_of_local {X : Type*} [Group X]
    {B S : Subgroup X} (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).surjective

private theorem perfect_to_solvable_eq_one {X Y : Type*} [Group X] [Group Y]
    [Group.IsPerfect X] [Group.IsSolvable Y] (f : X →* Y) : f = 1 := by
  by_contra hn
  have hk : f.range ≠ ⊥ := by
    exact fun he => hn (MonoidHom.range_eq_bot_iff.mp he)
  let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hk
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  exact Group.IsPerfect.not_isSolvable f.range inferInstance

/-- The projection to the nonsolvable Levi factor has a two-group kernel
on the original perfect local component. -/
private theorem local_projection {X Y Z : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] [Group Z] [Finite Z] [Group.IsSolvable Z]
    (f : X →* Y × Z) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 X) {B : Subgroup X} (hB : B ∈ localCComponents S) :
    let g := (MonoidHom.fst Y Z).comp f
    B.map g ∈ localCComponents (S.mapSurjective (f := g)
      ((show Function.Surjective (MonoidHom.fst Y Z) from fun x => ⟨(x,1),rfl⟩).comp hf)) ∧
    Nonempty ((B ⧸ pCore 2 B) ≃* (B.map g ⧸ pCore 2 (B.map g))) := by
  let g := (MonoidHom.fst Y Z).comp f
  let k : g.ker →* Z := ((MonoidHom.snd Y Z).comp f).comp g.ker.subtype
  have hkk : IsPGroup 2 k.ker := by
    let j : k.ker →* f.ker :=
      { toFun := fun x => ⟨x.val.val, Prod.ext x.val.property x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hk.of_injective j (fun x y hxy => Subtype.ext (Subtype.ext
      (congrArg (fun z : f.ker => (z : X)) hxy)))
  let : Group.IsNilpotent k.ker := hkk.isNilpotent
  let : Group.IsSolvable g.ker := Group.isSolvable_of_ker_le_range k.ker.subtype k (by simp)
  let := perfect_of_local hB
  have hz := perfect_to_solvable_eq_one (((MonoidHom.snd Y Z).comp f).comp B.subtype)
  have hgb : IsPGroup 2 (g.subgroupMap B).ker := by
    let j : (g.subgroupMap B).ker →* f.ker :=
      { toFun := fun x => ⟨x.val.val, Prod.ext
          (congrArg Subtype.val x.property) (DFunLike.congr_fun hz x.val)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hk.of_injective j (fun x y hxy => Subtype.ext (Subtype.ext
      (congrArg (fun z : f.ker => (z : X)) hxy)))
  exact ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hB g,
    ⟨(g.subgroupMap B).pCoreQuotientEquiv (g.subgroupMap_surjective B) hgb⟩⟩

/-- Every local C-component in GL_n(2), n≤5, has an actual binary
linear two-core quotient. The quotient is constructed through the Levi maps. -/
theorem local_twoCore_quotient (n : ℕ) (hn : n ≤ 5)
    (S : Sylow 2 (LinearGroup n)) (B : Subgroup (LinearGroup n))
    (hB : B ∈ localCComponents S) :
    ∃ m, 3 ≤ m ∧ m ≤ n ∧ Nonempty ((B ⧸ pCore 2 B) ≃* LinearGroup m) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n ≤ 2
    · let := small_solvable n hn2
      exact (hB.not_isSolvable inferInstance).elim
    have hn3 : 3 ≤ n := by omega
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
      Atlas.psl_simple_high_rank n hn3
    let : IsSimpleGroup (LinearGroup n) := (projectiveEquivLinear (by omega : 0<n)).symm.isSimpleGroup
    let : Group.IsPerfect (LinearGroup n) := linearGroup_isPerfect n hn3
    let J := B ⊔ (S : Subgroup (LinearGroup n))
    by_cases ht : J = ⊤
    · change (B.subgroupOf J).IsCComponent at hB
      have hsub : J.IsSubnormal := by rw [ht]; exact (inferInstance : (⊤ : Subgroup (LinearGroup n)).Normal).isSubnormal
      have hb : B.IsCComponent := by
        simpa only [map_subgroupOf_eq_of_le (show B ≤ J from le_sup_left)] using hB.map_subtype hsub
      let : IsSimpleGroup (⊤ : Subgroup (LinearGroup n)) := (topEquiv : (⊤ : Subgroup (LinearGroup n)) ≃* LinearGroup n).isSimpleGroup
      let : Group.IsPerfect (⊤ : Subgroup (LinearGroup n)) := Group.IsPerfect.ofSurjective
        (f := (topEquiv : (⊤ : Subgroup (LinearGroup n)) ≃* LinearGroup n).symm.toMonoidHom)
        topEquiv.symm.surjective
      have hbtop : B = ⊤ := hb.eq_of_le
        (Subgroup.isCComponent_of_isSimpleGroup_of_isPerfect
          (inferInstance : (⊤ : Subgroup (LinearGroup n)).Normal).isSubnormal) le_top
      let e : B ≃* LinearGroup n := (MulEquiv.subgroupCongr hbtop).trans topEquiv
      let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
      exact ⟨n,hn3,le_rfl,⟨q.trans ((QuotientGroup.quotientMulEquivOfEq
        (linearGroup_twoCore_eq_bot (V := Space n))).trans QuotientGroup.quotientBot)⟩⟩
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      obtain ⟨b,cuts,_,hcuts⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S J le_sup_right
      have hne : cuts.Nonempty := by
        by_contra hh
        have he := Set.not_nonempty_iff_eq_empty.mp hh
        apply ht
        rw [hcuts,he]
        ext g
        simp [mem_cutStabilizer]
      obtain ⟨i,hi⟩ := hne
      let W := cutSpace b i
      have hJW : J ≤ parabolic W := by
        rw [hcuts]
        intro g hg
        exact (mem_cutStabilizer b cuts g).mp hg i hi
      have hBW : B ≤ parabolic W := (show B ≤ J from le_sup_left).trans hJW
      have hSW : (S : Subgroup (LinearGroup (k+1))) ≤ parabolic W := le_sup_right.trans hJW
      let SP := S.subtype hSW
      let BP := B.subgroupOf (parabolic W)
      have hBP : BP ∈ localCComponents SP := local_restrict hB hBW
      let a : W ≃ₗ[ZMod 2] Space (i.val+1) := LinearEquiv.ofFinrankEq _ _ (by
        rw [Module.finrank_fin_fun]
        exact cutSpace_finrank b i)
      let c : (Space (k+1) ⧸ W) ≃ₗ[ZMod 2] Space (k-i.val) := LinearEquiv.ofFinrankEq _ _ (by
        rw [Module.finrank_fin_fun]
        have hd := W.finrank_quotient_add_finrank
        change Module.finrank (ZMod 2) (Space (k+1) ⧸ W) +
          Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (Space (k+1)) at hd
        rw [show Module.finrank (ZMod 2) W = i.val+1 from cutSpace_finrank b i,
          Module.finrank_fin_fun] at hd
        omega)
      let e := quotientTwoCoreEquivOfCoordinates W a c
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (parabolic W)))
      have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hk : IsPGroup 2 f.ker := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
        exact pCore_isPGroup
      let eb := subgroupOfEquivOfLe hBW
      let qb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
      by_cases hsmall : k-i.val ≤ 2
      · let := small_solvable (k-i.val) hsmall
        obtain ⟨hlocal,⟨q⟩⟩ := local_projection f hf hk SP hBP
        let g := (MonoidHom.fst (LinearGroup (i.val+1)) (LinearGroup (k-i.val))).comp f
        have hg : Function.Surjective g :=
          (show Function.Surjective (MonoidHom.fst (LinearGroup (i.val+1)) (LinearGroup (k-i.val)))
            from fun x => ⟨(x,1),rfl⟩).comp hf
        obtain ⟨m,hm,hmn,⟨j⟩⟩ := ih (i.val+1) (by have := i.isLt; omega)
          (by have := i.isLt; omega) (SP.mapSurjective (f := g) hg) (BP.map g) hlocal
        exact ⟨m,hm,by have := i.isLt; omega,⟨qb.symm.trans (q.trans j)⟩⟩
      · let := small_solvable (i.val+1) (by have := i.isLt; omega)
        let fc := (MulEquiv.prodComm : LinearGroup (i.val+1) × LinearGroup (k-i.val) ≃* LinearGroup (k-i.val) × LinearGroup (i.val+1)).toMonoidHom.comp f
        have hfc : Function.Surjective fc := MulEquiv.prodComm.surjective.comp hf
        have hkc : IsPGroup 2 fc.ker := by
          rw [MonoidHom.ker_comp_of_injective _ _ MulEquiv.prodComm.injective]
          exact hk
        obtain ⟨hlocal,⟨q⟩⟩ := local_projection fc hfc hkc SP hBP
        let g := (MonoidHom.fst (LinearGroup (k-i.val)) (LinearGroup (i.val+1))).comp fc
        have hg : Function.Surjective g :=
          (show Function.Surjective (MonoidHom.fst (LinearGroup (k-i.val)) (LinearGroup (i.val+1)))
            from fun x => ⟨(x,1),rfl⟩).comp hfc
        obtain ⟨m,hm,hmn,⟨j⟩⟩ := ih (k-i.val) (by omega)
          (by omega) (SP.mapSurjective (f := g) hg) (BP.map g) hlocal
        exact ⟨m,hm,by omega,⟨qb.symm.trans (q.trans j)⟩⟩

/-- Two comparable original local components use the same full intrinsic
Sylow in the larger one, even though it need not be subnormal in G. -/
theorem local_in_local_overgroup {X : Type*} [Group X] [Finite X]
    (T : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ localCComponents T) (hK : K ∈ localCComponents T) (hBK : B ≤ K) :
    ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup X).subgroupOf K ∧
      B.subgroupOf K ∈ localCComponents S := by
  let J := K ⊔ (T : Subgroup X)
  let TJ := T.subtype (show (T : Subgroup X) ≤ J from le_sup_right)
  obtain ⟨S,hS⟩ := TJ.exists_subgroupOf_eq_of_subnormal (K.subgroupOf J) hK.subnormal
  let e := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let SK := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : (SK : Subgroup K) = (T : Subgroup X).subgroupOf K := by
    change (S : Subgroup (K.subgroupOf J)).map e.toMonoidHom = _
    rw [hS]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x, (show K ≤ J from le_sup_left) x.property⟩,x.property⟩,hx,rfl⟩
  exact ⟨SK,he,he.symm ▸ local_restrict hB hBK⟩

/-- The original inclusion B≤K and the actual quotient map of K identify
the intrinsic two-core quotient of B as one of the binary smaller degrees. -/
theorem local_twoCore_quotient_of_containing_quotient
    {X : Type*} [Group X] [Finite X] (T : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ localCComponents T) (hK : K ∈ localCComponents T) (hBK : B ≤ K)
    (n : ℕ) (hn : n ≤ 5) (e : (K ⧸ pCore 2 K) ≃* LinearGroup n) :
    ∃ m, 3 ≤ m ∧ m ≤ n ∧ Nonempty ((B ⧸ pCore 2 B) ≃* LinearGroup m) := by
  obtain ⟨S,_,hlocal⟩ := local_in_local_overgroup T hB hK hBK
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  have hmap : (B.subgroupOf K).map f ∈ localCComponents (S.mapSurjective (f := f) hf) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f
  obtain ⟨m,hm,hmn,⟨a⟩⟩ := local_twoCore_quotient n hn (S.mapSurjective (f := f) hf) _ hmap
  let g := f.subgroupMap (B.subgroupOf K)
  have hkg : IsPGroup 2 g.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eb := subgroupOfEquivOfLe hBK
  let qb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  exact ⟨m,hm,hmn,⟨qb.symm.trans ((g.pCoreQuotientEquiv
    (f.subgroupMap_surjective _) hkg).trans a)⟩⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic
