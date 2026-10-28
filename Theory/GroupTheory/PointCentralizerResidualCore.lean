module
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Intrinsic point-centralizer residual cores

Taking the embedded two-residual of a point centralizer, then its two-core,
is functorial under group isomorphisms. Restriction to an ambient subgroup
preserves the exact centralizer intersection and subgroup maps. These identities
transport the original quaternion subgroup in Aschbacher–Smith 14.3.19(10).
-/

@[expose] public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

noncomputable def pointCentralizerTwoResidualCore (z:G) : Subgroup G :=
  ((pResidual 2 (centralizer ({z}:Set G))).map (centralizer ({z}:Set G)).subtype).pCoreIn 2

public theorem map_centralizer_singleton_equiv (e:G≃*H) (z:G) :
    (centralizer ({z}:Set G)).map e.toMonoidHom=centralizer ({e z}:Set H) := by
  ext x
  rw [mem_map_equiv,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
  constructor
  · intro hx
    simpa only [map_mul,MulEquiv.apply_symm_apply] using congrArg e hx
  · intro hx
    apply e.injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using hx

public theorem map_centralizer_singleton_subtype (K:Subgroup G) (z:K) :
    (centralizer ({z}:Set K)).map K.subtype=K⊓centralizer ({(z:G)}:Set G) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
  · rintro ⟨hxK,hxz⟩
    exact ⟨⟨x,hxK⟩,mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hxz)),rfl⟩

variable [Finite G]

public theorem map_pointCentralizerTwoResidualCore (e:G≃*H) (z:G) :
    (pointCentralizerTwoResidualCore z).map e.toMonoidHom=
      pointCentralizerTwoResidualCore (e z) := by
  unfold pointCentralizerTwoResidualCore
  rw [map_pCoreIn_of_injective 2 _ _ e.injective,map_embedded_pResidual,
    map_centralizer_singleton_equiv]

public theorem map_pointCentralizerTwoResidualCore_subtype (K:Subgroup G) (z:K) :
    (pointCentralizerTwoResidualCore z).map K.subtype=
      ((pResidual 2 (K⊓centralizer ({(z:G)}:Set G):Subgroup G)).map
        (K⊓centralizer ({(z:G)}:Set G)).subtype).pCoreIn 2 := by
  unfold pointCentralizerTwoResidualCore
  rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective,map_embedded_pResidual,
    map_centralizer_singleton_subtype]

public theorem pointCentralizerTwoResidualCore_eq_subgroupOf
    (K U:Subgroup G) (z:K) (hU:U≤K)
    (hcore:((pResidual 2 (K⊓centralizer ({(z:G)}:Set G):Subgroup G)).map
      (K⊓centralizer ({(z:G)}:Set G)).subtype).pCoreIn 2=U) :
    pointCentralizerTwoResidualCore z=U.subgroupOf K := by
  apply map_injective K.subtype_injective
  rw [map_pointCentralizerTwoResidualCore_subtype,hcore,map_subgroupOf_eq_of_le hU]

end Subgroup
