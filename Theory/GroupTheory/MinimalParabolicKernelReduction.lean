module
public import Theory.GroupTheory.MinimalParabolicFrattiniKernel

/-!
# Normal kernels below a unique Sylow maximal subgroup

A normal subgroup containing the two-core and generating a proper subgroup
with a Sylow two-subgroup has that two-core as its Sylow intersection. Its
image modulo the core is an odd nilpotent Frattini subgroup. Consequently,
every supplement of the original normal subgroup also supplements the core.
For a non-two simple quotient, simplicity supplies the containment of the
core and the properness condition automatically.

The proof uses the normal Sylow intersection and Frattini argument in
`MinimalParabolicFrattiniKernel`. The original normal kernel is retained;
no equality of that kernel with the two-core is assumed.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 2.2. The rank-one
application is in `Theory.SpecificGroups.SL2.UniqueMaximalKernel`.
-/

public section
open Subgroup
namespace Theory.GroupTheory.MinimalParabolicKernel
variable {H : Type*} [Group H] [Finite H]

theorem kernel_sylow_intersection (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] (hQK : pCore 2 H ≤ K)
    (hproper : K ⊔ (S : Subgroup H) < ⊤) :
    (S : Subgroup H) ⊓ K = pCore 2 H := by
  obtain ⟨M,hM,_⟩ := hu.2
  have hKM := le_sup_left.trans (hu.le_maximal hM le_sup_right hproper)
  exact le_antisymm
    (sylow_inf_normal_le_twoCore_of_uniqueMaximal S hu M K ⟨hM.1,hM.2.isCoatom⟩ hKM)
    (le_inf (pCore_isPGroup.le_sylow_of_normal S) hQK)

theorem kernel_image_nilpotent (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] (hQK : pCore 2 H ≤ K)
    (hproper : K ⊔ (S : Subgroup H) < ⊤) :
    Group.IsNilpotent (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  let N := K.map (QuotientGroup.mk' (pCore 2 H))
  have hNF : N ≤ frattini (H ⧸ pCore 2 H) :=
    normal_image_le_frattini_of_uniqueMaximal S hu K hQK hproper
  let _ := frattini_nilpotent (G := H ⧸ pCore 2 H)
  exact (Group.isNilpotent_congr (subgroupOfEquivOfLe hNF)).mp inferInstance

theorem kernel_supplement_reduces_to_core (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] (hQK : pCore 2 H ≤ K)
    (hproper : K ⊔ (S : Subgroup H) < ⊤)
    (L : Subgroup H) (hLK : L ⊔ K = ⊤) : L ⊔ pCore 2 H = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq := QuotientGroup.mk'_surjective (pCore 2 H)
  have hKF := normal_image_le_frattini_of_uniqueMaximal S hu K hQK hproper
  have hLt : L.map q = ⊤ := by
    apply frattini_nongenerating
    apply top_unique
    rw [←map_top_of_surjective q hq,←hLK,Subgroup.map_sup]
    exact sup_le_sup_left hKF _
  have hh := congrArg (Subgroup.comap q) hLt
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk',comap_top] using hh

theorem kernel_image_odd (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] (hQK : pCore 2 H ≤ K)
    (hproper : K ⊔ (S : Subgroup H) < ⊤) :
    ¬ 2 ∣ Nat.card (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hPK : (pCore 2 H).subgroupOf K = (P : Subgroup K) := by
    rw [←kernel_sylow_intersection S hu K hQK hproper,hP]
    ext x
    exact and_iff_left x.property
  have hc : Nat.card (K.map (QuotientGroup.mk' (pCore 2 H))) = P.index := by
    rw [←relIndex_ker K (QuotientGroup.mk' (pCore 2 H)),QuotientGroup.ker_mk',relIndex,hPK]
  rw [hc]
  exact P.not_dvd_index

variable {A : Type*} [Group A]

omit [Finite H] in
theorem kernel_sup_sylow_lt_top (S : Sylow 2 H)
    (f : H →* A) (hf : Function.Surjective f) (hA : ¬ IsPGroup 2 A) :
    f.ker ⊔ (S : Subgroup H) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  have hi : (S : Subgroup H).map f = ⊤ := by
    have hh := congrArg (Subgroup.map f) he
    have hk : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff f.ker).mpr le_rfl
    simpa only [Subgroup.map_sup,hk,map_top_of_surjective f hf,bot_sup_eq] using hh
  have hp := S.isPGroup'.map f
  rw [hi] at hp
  exact hA (hp.of_equiv Subgroup.topEquiv)

omit [Finite H] in
theorem core_le_simple_kernel [IsSimpleGroup A]
    (f : H →* A) (hf : Function.Surjective f) (hA : ¬ IsPGroup 2 A) :
    pCore 2 H ≤ f.ker := by
  have hn := (inferInstance : (pCore 2 H).Normal).map f hf
  have hp := (pCore_isPGroup (G := H) (p := 2)).map f
  apply (Subgroup.map_eq_bot_iff _).mp
  exact hn.eq_bot_or_eq_top.resolve_right (fun he => hA
    ((he ▸ hp).of_equiv Subgroup.topEquiv))

theorem simple_quotient_kernel_reduction [IsSimpleGroup A]
    (S : Sylow 2 H) (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (f : H →* A) (hf : Function.Surjective f) (hA : ¬ IsPGroup 2 A) :
    (S : Subgroup H) ⊓ f.ker = pCore 2 H ∧
    f.ker.map (QuotientGroup.mk' (pCore 2 H)) ≤ frattini (H ⧸ pCore 2 H) ∧
    Group.IsNilpotent (f.ker.map (QuotientGroup.mk' (pCore 2 H))) ∧
    (¬ 2 ∣ Nat.card (f.ker.map (QuotientGroup.mk' (pCore 2 H)))) ∧
    ∀ L : Subgroup H, L ⊔ f.ker = ⊤ → L ⊔ pCore 2 H = ⊤ := by
  have hQK := core_le_simple_kernel f hf hA
  have hproper := kernel_sup_sylow_lt_top S f hf hA
  exact ⟨kernel_sylow_intersection S hu f.ker hQK hproper,
    normal_image_le_frattini_of_uniqueMaximal S hu f.ker hQK hproper,
    kernel_image_nilpotent S hu f.ker hQK hproper,
    kernel_image_odd S hu f.ker hQK hproper,
    kernel_supplement_reduces_to_core S hu f.ker hQK hproper⟩

/-- The original normal kernel, expressed through its literal quotient map. -/
theorem quotient_kernel_reduction (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K)) :
    (S : Subgroup H) ⊓ K = pCore 2 H ∧
    K.map (QuotientGroup.mk' (pCore 2 H)) ≤ frattini (H ⧸ pCore 2 H) ∧
    Group.IsNilpotent (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
    (¬ 2 ∣ Nat.card (K.map (QuotientGroup.mk' (pCore 2 H)))) ∧
    ∀ L : Subgroup H, L ⊔ K = ⊤ → L ⊔ pCore 2 H = ⊤ := by
  have hQK : pCore 2 H ≤ K := by
    simpa only [QuotientGroup.ker_mk'] using
      core_le_simple_kernel (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hK
  have hproper : K ⊔ (S : Subgroup H) < ⊤ := by
    simpa only [QuotientGroup.ker_mk'] using
      kernel_sup_sylow_lt_top S (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hK
  exact ⟨kernel_sylow_intersection S hu K hQK hproper,
    normal_image_le_frattini_of_uniqueMaximal S hu K hQK hproper,
    kernel_image_nilpotent S hu K hQK hproper,
    kernel_image_odd S hu K hQK hproper,
    kernel_supplement_reduces_to_core S hu K hQK hproper⟩

end Theory.GroupTheory.MinimalParabolicKernel
