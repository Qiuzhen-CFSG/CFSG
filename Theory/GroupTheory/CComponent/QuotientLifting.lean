module

public import Theory.GroupTheory.CComponent.LayerTransport
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreRestriction
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Lifting C-components and their normalizers through solvable quotients

A perfect subgroup contained in the image of a C-component lifts into that
C-component: take the solvable residual of its product with the kernel.
The bijection on C-components also identifies their normalizers and their
conjugacy-orbit lengths. These facts lift generation by C-components and
commutation modulo the two-core. The intrinsic two-core quotient of a
C-component is identified with its image in the ambient two-core quotient.

These are general finite-group deductions used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Proposition 1.2.1 and Lemma 1.2.4,
pp. 503–505 (combined manuscript, 1 March 2004), from A.3.3(3)–(6).
No SQTK classification result is assumed in this module.
-/

@[expose] public section
open scoped Pointwise
namespace Subgroup
universe u v
variable {G : Type u} {G' : Type v} [Group G] [Group G'] [Finite G]

/-- A surjection with solvable kernel preserves C-components. -/
theorem cComponent_map_of_solvable_ker {B : Subgroup G} (hB : B.IsCComponent)
    (f : G →* G') (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    (B.map f).IsCComponent := by
  have h := (hB.map_quotient f.ker).map_equiv
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  rw [map_map] at h
  exact h

/-- Containment of a perfect subgroup in a C-component can be tested modulo a solvable normal subgroup. -/
theorem perfect_le_cComponent_of_map_le {B K : Subgroup G} [Group.IsPerfect B]
    (hK : K.IsCComponent) (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hle : B.map (QuotientGroup.mk' N) ≤ K.map (QuotientGroup.mk' N)) : B ≤ K := by
  have hBN : B ≤ K ⊔ N := by
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using map_le_iff_le_comap.mp hle
  have hres := le_map_solvableResidual_of_isPerfect B (K ⊔ N) hBN
  rwa [hK.solvableResidual_sup_eq N (by rw [normalizer_eq_top]; exact le_top)] at hres

/-- Unique containment in a C-component lifts through a solvable quotient. -/
theorem existsUnique_cComponent_lift_containing {B : Subgroup G} [Group.IsPerfect B]
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (h : ∃! K : Subgroup (G ⧸ N), K.IsCComponent ∧ B.map (QuotientGroup.mk' N) ≤ K) :
    ∃! K : Subgroup G, K.IsCComponent ∧ B ≤ K := by
  obtain ⟨Kbar, hKbar, hu⟩ := h
  obtain ⟨K, hK, he⟩ := hKbar.1.exists_map_quotient_eq N
  refine ⟨K, ⟨hK, perfect_le_cComponent_of_map_le hK N (he.symm ▸ hKbar.2)⟩, ?_⟩
  intro D hD
  exact hD.1.eq_of_map_quotient_eq hK N ((hu _ ⟨hD.1.map_quotient N,
    map_mono hD.2⟩).trans he.symm)

/-- The normalizer of a quotient C-component pulls back to the original normalizer. -/
theorem normalizer_cComponent_quotient {K : Subgroup G} (hK : K.IsCComponent)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] :
    (normalizer (K.map (QuotientGroup.mk' N))).comap (QuotientGroup.mk' N) =
      normalizer (K : Set G) := by
  let q := QuotientGroup.mk' N
  apply le_antisymm
  · intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply (hK.map_equiv (MulAut.conj g)).eq_of_map_quotient_eq hK N
    have he : q.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (q g)).toMonoidHom.comp q := by ext; simp [q]
    rw [map_map, he, ← map_map]
    exact mem_normalizer_iff_map_conj_eq.mp hg
  · exact map_le_iff_le_comap.mp (le_normalizer_map _)

/-- Normality of a C-component is reflected by a solvable quotient. -/
theorem cComponent_normal_of_quotient_normal {K : Subgroup G} (hK : K.IsCComponent)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hn : (K.map (QuotientGroup.mk' N)).Normal) : K.Normal := by
  rw [← normalizer_eq_top_iff, ← normalizer_cComponent_quotient hK N]
  let := hn
  rw [normalizer_eq_top, comap_top]

/-- A solvable quotient preserves the conjugacy-orbit length of a C-component. -/
theorem cComponent_normalizer_index_quotient {K : Subgroup G} (hK : K.IsCComponent)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] :
    (normalizer (K.map (QuotientGroup.mk' N) : Set (G ⧸ N))).index =
      (normalizer (K : Set G)).index := by
  rw [← normalizer_cComponent_quotient hK N,
    index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]

/-- A solvable quotient carries the C-component layer onto the quotient layer. -/
theorem cComponentLayer_map_quotient (N : Subgroup G) [N.Normal] [Group.IsSolvable N] :
    (cComponentLayer G).map (QuotientGroup.mk' N) = cComponentLayer (G ⧸ N) := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    exact sSup_le fun B hB => map_le_iff_le_comap.mp (le_cComponentLayer (hB.map_quotient N))
  · apply sSup_le
    intro K hK
    obtain ⟨B, hB, rfl⟩ := hK.exists_map_quotient_eq N
    exact map_mono (le_cComponentLayer hB)

/-- Every C-component is normal in the subgroup generated by all C-components (A.3.3(6)). -/
theorem cComponentLayer_le_normalizer {K : Subgroup G} (hK : K.IsCComponent) :
    cComponentLayer G ≤ normalizer (K : Set G) := by
  rw [← normalizer_cComponent_quotient hK (solvableRadical G)]
  apply map_le_iff_le_comap.mp
  rw [cComponentLayer_map_quotient]
  exact (hK.map_quotient (solvableRadical G)).sSup_isCComponent_le_normalizer_of_solvableRadical_eq_bot
    (solvableRadical_quotient_solvableRadical (G := G))

omit [Finite G] in
/-- The normalizer of a subgroup normalizes its unique containing C-component. -/
theorem cComponent_le_normalizer_of_unique {B K : Subgroup G} (hK : K.IsCComponent)
    (hBK : B ≤ K) (hu : ∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K)
    {S : Subgroup G} (hSB : S ≤ normalizer B) : S ≤ normalizer (K : Set G) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply hu _ (hK.map_equiv (MulAut.conj s))
  have hfix := mem_normalizer_iff_map_conj_eq.mp (hSB hs)
  exact hfix ▸ map_mono (f := (MulAut.conj s).toMonoidHom) hBK

/-- A Sylow two-subgroup cannot normalize one of exactly two conjugate C-components. -/
theorem cComponent_normal_of_unique_of_orbit_two {B K : Subgroup G}
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (hu : ∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K)
    (S : Sylow 2 G) (hSB : (S : Subgroup G) ≤ normalizer B)
    (horbit : K.Normal ∨ (normalizer (K : Set G)).index = 2) : K.Normal := by
  rcases horbit with hn | hi
  · exact hn
  · have hSN := cComponent_le_normalizer_of_unique hK hBK hu hSB
    have hd := index_dvd_of_le hSN
    rw [hi] at hd
    exact (S.not_dvd_index hd).elim

omit [Finite G] in
/-- The subgroup generated by all C-components is perfect. -/
theorem cComponentLayer_isPerfect : Group.IsPerfect (cComponentLayer G) := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm (cComponentLayer G).commutator_le_self
  apply sSup_le
  intro B hB
  have he : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hB.perfect
  exact he.symm.le.trans (commutator_mono (le_cComponentLayer hB) (le_cComponentLayer hB))

/-- Generation of the solvable residual by C-components lifts from a solvable quotient. -/
theorem cComponentLayer_eq_residual_of_quotient (N : Subgroup G) [N.Normal]
    [Group.IsSolvable N]
    (he : cComponentLayer (G ⧸ N) = solvableResidual (G ⧸ N)) :
    cComponentLayer G = solvableResidual G := by
  let := cComponentLayer_isPerfect (G := G)
  let := cComponentLayer_characteristic (G := G)
  have hmap : (solvableResidual G).map (QuotientGroup.mk' N) =
      (cComponentLayer G).map (QuotientGroup.mk' N) := by
    rw [map_solvableResidual_eq _ (QuotientGroup.mk'_surjective N),
      cComponentLayer_map_quotient N, he]
  have hle : solvableResidual G ≤ cComponentLayer G ⊔ N := by
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using map_le_iff_le_comap.mp hmap.le
  have hr := le_map_solvableResidual_of_isPerfect (solvableResidual G)
    (cComponentLayer G ⊔ N) hle
  rw [(inferInstance : (cComponentLayer G).Normal).isSubnormal.solvableResidual_sup_eq N
    (by rw [normalizer_eq_top]; exact le_top)] at hr
  exact le_antisymm (le_solvableResidual_of_isPerfect _) hr

/-- The intrinsic p-core of a subnormal subgroup lies in the ambient p-core. -/
theorem pCoreIn_le_of_subnormal (p : ℕ) {B : Subgroup G} (hB : B.IsSubnormal) :
    B.pCoreIn p ≤ pCore p G := by
  have h := pCoreAmbient_mono_of_isSubnormalIn B ⊤ p le_top hB.subgroupOf
  change B.pCoreIn p ≤ (pCore p (⊤ : Subgroup G)).map
    (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom at h
  rwa [pCore_map_iso] at h

/-- The intrinsic p-core of a subnormal subgroup is its intersection with the ambient p-core. -/
theorem pCore_subnormal_eq_comap (p : ℕ) {B : Subgroup G} (hB : B.IsSubnormal) :
    pCore p B = (pCore p G).comap B.subtype := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mp (pCoreIn_le_of_subnormal p hB)
  · exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective⟩

/-- The two-core quotient of a C-component is its actual image in the ambient two-core quotient. -/
noncomputable def cComponentTwoCoreQuotientEquiv {B : Subgroup G} (hB : B.IsCComponent) :
    (B ⧸ pCore 2 B) ≃* B.map (QuotientGroup.mk' (pCore 2 G)) := by
  let f := (QuotientGroup.mk' (pCore 2 G)).subgroupMap B
  have he : f.ker = pCore 2 B := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hB.subnormal).symm
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pCore 2 G)).subgroupMap_surjective B))

/-- Commutation in the two-core quotient lifts to the two intrinsic two-cores. -/
theorem cComponent_commutator_le_twoCores_of_quotient_commutes
    {B K : Subgroup G} (hB : B.IsCComponent) (hK : K.IsCComponent)
    (hcomm : ⁅B.map (QuotientGroup.mk' (pCore 2 G)),
      K.map (QuotientGroup.mk' (pCore 2 G))⁆ = ⊥) :
    ⁅B, K⁆ ≤ B.pCoreIn 2 ⊓ K.pCoreIn 2 ∧
      B.pCoreIn 2 ⊓ K.pCoreIn 2 ≤ pCore 2 G := by
  have hc : ⁅B, K⁆ ≤ pCore 2 G := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hcomm
    exact hcomm
  have hp : IsPGroup 2 ↥(⁅B, K⁆ : Subgroup G) := pCore_isPGroup.to_le hc
  have hBK : B ≤ normalizer (K : Set G) := (le_cComponentLayer hB).trans (cComponentLayer_le_normalizer hK)
  have hKB : K ≤ normalizer B := (le_cComponentLayer hK).trans (cComponentLayer_le_normalizer hB)
  refine ⟨le_inf ?_ ?_, inf_le_left.trans (pCoreIn_le_of_subnormal 2 hB.subnormal)⟩
  · exact le_pCoreIn_of_normalizes hp (le_normalizer_iff_commutator_le_left.mp hKB)
      (normalizer_commutator_ge_left B K)
  · exact le_pCoreIn_of_normalizes hp (le_normalizer_iff_commutator_le_right.mp hBK)
      (normalizer_commutator_ge_right B K)

/-- Factoring out the p-core leaves trivial p-core. -/
theorem pCore_quotient_pCore_eq_bot (p : ℕ) [Fact p.Prime] :
    pCore p (G ⧸ pCore p G) = ⊥ := by
  let q := QuotientGroup.mk' (pCore p G)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup p q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := q.comap_pCore_of_ker_isPGroup hq hk
  have hm := congrArg (map q) he
  rw [map_comap_eq_self_of_surjective hq] at hm
  exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

/-- Lift a specified quotient C-component while retaining perfect-subgroup containment and the exact image. -/
theorem exists_cComponent_lift_containing_map {B : Subgroup G} [Group.IsPerfect B]
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    {Kbar : Subgroup (G ⧸ N)} (hKbar : Kbar.IsCComponent)
    (hle : B.map (QuotientGroup.mk' N) ≤ Kbar) :
    ∃ K : Subgroup G, K.IsCComponent ∧ B ≤ K ∧ K.map (QuotientGroup.mk' N) = Kbar := by
  obtain ⟨K, hK, he⟩ := hKbar.exists_map_quotient_eq N
  exact ⟨K, hK, perfect_le_cComponent_of_map_le hK N (he.symm ▸ hle), he⟩

/-- The normal-or-two-conjugates alternative lifts through a solvable quotient. -/
theorem cComponent_normal_or_index_two_of_quotient {B : Subgroup G}
    (hB : B.IsCComponent) (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (h : (B.map (QuotientGroup.mk' N)).Normal ∨
      (normalizer (B.map (QuotientGroup.mk' N) : Set (G ⧸ N))).index = 2) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 := by
  rcases h with hn | hi
  · exact Or.inl (cComponent_normal_of_quotient_normal hB N hn)
  · exact Or.inr ((cComponent_normalizer_index_quotient hB N).symm.trans hi)

omit [Finite G] in
/-- The set of conjugate subgroups has cardinality equal to the normalizer index. -/
theorem ncard_conjugates_eq_index_normalizer (B : Subgroup G) :
    (Set.range fun g : G => B.map (MulAut.conj g).toMonoidHom).ncard =
      (normalizer (B : Set G)).index := by
  let : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) MulAut.conj
  have he : normalizer (B : Set G) = MulAction.stabilizer G B := by
    ext g
    exact mem_normalizer_iff_map_conj_eq
  rw [he, MulAction.index_stabilizer]
  rfl

end Subgroup
