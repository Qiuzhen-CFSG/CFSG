module

public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Central kernels modulo prime cores

For a central-kernel map, the inverse image of the target p-core is a normal
nilpotent subgroup. Its Sylow p-subgroup lies in the source p-core and its
p-residual lies in the center. This proves centrality after removing p-cores.
The same conclusion holds when the original kernel is only central modulo
the source p-core: first remove the image of that core in the target.

Centrality modulo a prime core restricts along arbitrary injective maps,
since the inverse image of the ambient core lies in the intrinsic core.
These results do not require the original kernel to be a p-group.

The nilpotent-preimage argument follows the existing private proof in
`CyclicCoreQuotient.lean`; it is exposed here without its cyclic-quotient
specialization, while preserving that module's existing public boundary.
Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.19, printed p.931, for the intrinsic-to-action maps of flag residuals.
-/

public section

open Subgroup
open scoped commutatorElement
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
  {p : ℕ} [Fact p.Prime]

/-- A central extension pulls a prime core into the source core times its center. -/
theorem central_preimage_pCore_le (f : G →* H)
    (hk : f.ker ≤ center G) : (pCore p H).comap f ≤ pCore p G ⊔ center G := by
  let L := (pCore p H).comap f
  let r : L →* pCore p H := (f.comp L.subtype).codRestrict _ (fun x => x.property)
  have hrk : r.ker ≤ center L := by
    intro x hx
    have hfx : f x.val = 1 := congrArg (fun a : pCore p H => (a : H)) (show r x = 1 from hx)
    have hc := hk hfx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hc y.val)
  let : Group.IsNilpotent (pCore p H) := (pCore_isPGroup (p := p) (G := H)).isNilpotent
  let : Group.IsNilpotent L := Subgroup.isNilpotent_of_ker_le_center r hrk
  let T : Sylow p L := Classical.choice inferInstance
  have hTnormal : ((T : Subgroup L).map L.subtype).Normal :=
    Sylow.normal_of_nilpotent_normal (inferInstance : L.Normal) inferInstance p T
  have hTcore : (T : Subgroup L).map L.subtype ≤ pCore p G :=
    le_sSup ⟨hTnormal, T.isPGroup'.map L.subtype⟩
  have hrquot : IsPGroup p (L ⧸ r.ker) :=
    ((pCore_isPGroup (p := p) (G := H)).to_subgroup r.range).of_equiv
      (QuotientGroup.quotientKerEquivRange r).symm
  have hres : pResidual p L ≤ r.ker := sInf_le ⟨inferInstance, hrquot⟩
  have hresZ : (pResidual p L).map L.subtype ≤ center G := by
    rintro _ ⟨x, hx, rfl⟩
    apply hk
    exact congrArg (fun a : pCore p H => (a : H)) (show r x = 1 from hres hx)
  have he := congrArg (fun D : Subgroup L => D.map L.subtype) (pResidual_sup_sylow_eq_top T)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  change L ≤ pCore p G ⊔ center G
  rw [← he]
  exact sup_le (hresZ.trans le_sup_right) (hTcore.trans le_sup_left)

/-- Removing the target prime core preserves centrality of the kernel modulo
the source prime core. -/
theorem coreMap_ker_le_center_of_map_ker
    (f : G →* H) (hf : Function.Surjective f)
    (hc : pCore p G ≤ (pCore p H).comap f)
    (hk : f.ker.map (QuotientGroup.mk' (pCore p G)) ≤ center (G ⧸ pCore p G)) :
    (QuotientGroup.map (pCore p G) (pCore p H) f hc).ker ≤
      center (G ⧸ pCore p G) := by
  let N := (pCore p G).map f
  let : N.Normal := Normal.map inferInstance f hf
  let q := QuotientGroup.mk' (pCore p G)
  let a := QuotientGroup.map (pCore p G) N f (le_comap_map f (pCore p G))
  have hak : a.ker ≤ center (G ⧸ pCore p G) := by
    rw [QuotientGroup.ker_map]
    change (((pCore p G).map f).comap f).map q ≤ _
    rw [comap_map_eq, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    exact hk
  have ha := central_preimage_pCore_le (p := p) a hak
  rw [pCore_quotient_pCore_eq_bot, bot_sup_eq] at ha
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore p G) x
  apply ha
  change QuotientGroup.mk' N (f y) ∈ pCore p (H ⧸ N)
  have hy : f y ∈ pCore p H := (QuotientGroup.eq_one_iff (f y)).mp hx
  have hm : (pCore p H).map (QuotientGroup.mk' N) ≤ pCore p (H ⧸ N) :=
    le_sSup ⟨Normal.map inferInstance _ (QuotientGroup.mk'_surjective N),
      pCore_isPGroup.map _⟩
  exact hm (mem_map_of_mem _ hy)

omit [Finite G] [Finite H] [Fact p.Prime] in
/-- Centrality modulo a prime core restricts along an injective homomorphism. -/
theorem comap_central_mod_pCore_of_injective
    {A : Type*} [Group A] (i : A →* G) (hi : Function.Injective i)
    (N : Subgroup G)
    (hk : N.map (QuotientGroup.mk' (pCore p G)) ≤ center (G ⧸ pCore p G)) :
    (N.comap i).map (QuotientGroup.mk' (pCore p A)) ≤
      center (A ⧸ pCore p A) := by
  have hcore : (pCore p G).comap i ≤ pCore p A :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i hi⟩
  rintro _ ⟨x, hx, rfl⟩
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore p A) y
  have hz := hk (mem_map_of_mem (QuotientGroup.mk' (pCore p G)) hx)
  have hcomm : i ⁅y, x⁆ ∈ pCore p G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore p G) (i ⁅y, x⁆) = 1
    rw [map_commutatorElement, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz _)
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr (hcore hcomm)

omit [Finite G] [Finite H] [Fact p.Prime] in
/-- A nontrivial image of a quasisimple core quotient has central kernel. -/
theorem map_ker_central_of_quasisimple_pCore
    [Theory.GroupTheory.IsQuasisimple (G ⧸ pCore p G)] [Nontrivial H]
    (f : G →* H) (hf : Function.Surjective f) (hc : pCore p G ≤ f.ker) :
    f.ker.map (QuotientGroup.mk' (pCore p G)) ≤ center (G ⧸ pCore p G) := by
  let a := QuotientGroup.lift (pCore p G) f hc
  have ha : Function.Surjective a := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  have hk : a.ker ≤ center (G ⧸ pCore p G) := by
    rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top a.ker with h | h
    · exact h
    · have htriv : ∀ x : H, x = 1 := by
        intro x
        obtain ⟨y, rfl⟩ := ha x
        have hy : y ∈ a.ker := by rw [h]; exact mem_top y
        exact hy
      obtain ⟨x, hx⟩ := exists_ne (1 : H)
      exact (hx (htriv x)).elim
  rintro _ ⟨x, hx, rfl⟩
  exact hk hx
end MonoidHom
