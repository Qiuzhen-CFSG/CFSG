module

public import Theory.GroupTheory.QuasithinBasic
public import Theory.PGroupCore
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.SimpleSectionNormalAlternative

/-!
# The quasithin main hypothesis

The definitions follow Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript of 1 March 2004, §0.1 (pp. 3–4, 481–483),
§A.2 and §A.3. Quasithin uses the existing invariant `e`; strongly quasithin
bounds every odd prime rank. Even characteristic tests maximal 2-locals
containing a Sylow 2-subgroup, not all maximal 2-locals.

The parameter `K` denotes the full class of known finite simple groups. It is
intentionally explicit: no classification or restricted QTKE output list is
built into this interface. A K-group has all its simple sections in `K`.
Sections are represented by surjections from actual subgroups; the first
isomorphism theorem identifies these with quotients by normal subgroups.
This expresses the source's composition-factor condition for every subgroup.
The concrete interpretation of `K` is supplied by the model development.

The bridges below use rank monotonicity and maximal 2-local overgroups.
-/

@[expose] public section

namespace CFSG.Quasithin

universe u

/-- A class of groups, to be instantiated with the full known-simple universe. -/
abbrev GroupClass := (S : Type u) → [Group S] → Prop

/-- Every odd prime rank is at most two (condition SQT). -/
def IsStronglyQuasithin (G : Type*) [Group G] : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2

/-- Every simple section of every subgroup belongs to the specified class.
There is no classification assumption on the parameter `K`. -/
def IsKGroup (K : GroupClass.{u}) (G : Type u) [Group G] : Prop :=
  ∀ (S : Type u) [Group S], IsSimpleGroup S →
    ∀ (U : Subgroup G) (f : U →* S), Function.Surjective f → K S

/-- The induction hypothesis (K) applies to all proper subgroups. -/
def HasProperKSubgroups (K : GroupClass.{u}) (G : Type u) [Group G] : Prop :=
  ∀ U : Subgroup G, U ≠ ⊤ → IsKGroup K U

/-- A group of characteristic two has self-centralizing 2-core. -/
def HasCharacteristicTwo (G : Type*) [Group G] : Prop :=
  Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G

/-- Condition (E) relative to the fixed Sylow subgroup used in the source. -/
def IsEvenCharacteristicAt {G : Type*} [Group G] (T : Sylow 2 G) : Prop :=
  ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
    HasCharacteristicTwo M

/-- Even characteristic, stated without choosing a Sylow subgroup. -/
def IsEvenCharacteristic (G : Type*) [Group G] : Prop :=
  ∀ T : Sylow 2 G, IsEvenCharacteristicAt T

/-- An SQTK-group is strongly quasithin and a K-group (§A.2). -/
structure IsSQTK (K : GroupClass.{u}) (G : Type u) [Group G] : Prop where
  stronglyQuasithin : IsStronglyQuasithin G
  isKGroup : IsKGroup K G

/-- The three clauses of Main Hypothesis 0.1.1 in Volume I. -/
structure IsQTKE (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop where
  quasithin : IsQuasithin G
  properK : HasProperKSubgroups K G
  evenCharacteristic : IsEvenCharacteristic G

/-- The nonabelian simple groups in the main classification theorem. -/
structure IsSimpleQTKE (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop
    extends IsQTKE K G where
  simple : IsSimpleGroup G
  nonabelian : ¬ IsMulCommutative G

variable {G H : Type u} [Group G] [Group H]

theorem isQuasithin_iff_twoLocal [Finite G] :
    IsQuasithin G ↔ ∀ M : Subgroup G, IsTwoLocal M → IsStronglyQuasithin M :=
  Theory.GroupTheory.isQuasithin_iff_twoLocal

theorem IsStronglyQuasithin.of_injective [Finite G] [Finite H]
    (h : IsStronglyQuasithin H) (f : G →* H) (hf : Function.Injective f) :
    IsStronglyQuasithin G := by
  intro p hp ho
  exact (Theory.GroupTheory.primeRank_le_of_injective p f hf).trans (h p hp ho)

theorem IsStronglyQuasithin.subgroup [Finite G]
    (h : IsStronglyQuasithin G) (U : Subgroup G) : IsStronglyQuasithin U :=
  h.of_injective U.subtype U.subtype_injective

theorem IsStronglyQuasithin.quasithin [Finite G]
    (h : IsStronglyQuasithin G) : IsQuasithin G :=
  isQuasithin_iff_twoLocal.mpr fun M _ => h.subgroup M

theorem IsStronglyQuasithin.equiv [Finite G] [Finite H]
    (e : G ≃* H) : IsStronglyQuasithin G ↔ IsStronglyQuasithin H :=
  ⟨fun h => h.of_injective e.symm.toMonoidHom e.symm.injective,
    fun h => h.of_injective e.toMonoidHom e.injective⟩

theorem IsKGroup.of_injective {K : GroupClass.{u}}
    (h : IsKGroup K H) (f : G →* H) (hf : Function.Injective f) : IsKGroup K G := by
  intro S _ hS U g hg
  let e := Subgroup.equivMapOfInjective U f hf
  exact h S hS (U.map f) (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective)

theorem IsKGroup.subgroup {K : GroupClass.{u}}
    (h : IsKGroup K G) (U : Subgroup G) : IsKGroup K U :=
  h.of_injective U.subtype U.subtype_injective

theorem IsKGroup.equiv {K : GroupClass.{u}} (e : G ≃* H) :
    IsKGroup K G ↔ IsKGroup K H :=
  ⟨fun h => h.of_injective e.symm.toMonoidHom e.symm.injective,
    fun h => h.of_injective e.toMonoidHom e.injective⟩

theorem IsKGroup.of_surjective {K : GroupClass.{u}}
    (h : IsKGroup K G) (f : G →* H) (hf : Function.Surjective f) : IsKGroup K H := by
  intro S _ hS U g hg
  let V := U.comap f
  let q : V →* U := f.subgroupComap U
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective U hf
  exact h S hS V (g.comp q) (hg.comp hq)

theorem IsKGroup.quotient {K : GroupClass.{u}} (h : IsKGroup K G)
    (N : Subgroup G) [N.Normal] : IsKGroup K (G ⧸ N) :=
  h.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem IsKGroup.properK {K : GroupClass.{u}}
    (h : IsKGroup K G) : HasProperKSubgroups K G := fun U _ => h.subgroup U

theorem IsSQTK.subgroup [Finite G] {K : GroupClass.{u}}
    (h : IsSQTK K G) (U : Subgroup G) : IsSQTK K U :=
  ⟨h.stronglyQuasithin.subgroup U, h.isKGroup.subgroup U⟩

theorem IsQTKE.twoLocal_sqtk [Finite G] {K : GroupClass.{u}}
    (h : IsQTKE K G) (M : Subgroup G) (hM : IsTwoLocal M) (hproper : M ≠ ⊤) :
    IsSQTK K M :=
  ⟨isQuasithin_iff_twoLocal.mp h.quasithin M hM, h.properK M hproper⟩

theorem IsQTKE.involution_centralizer_stronglyQuasithin [Finite G]
    {K : GroupClass.{u}} (h : IsQTKE K G) {t : G} (ht : orderOf t = 2) :
    IsStronglyQuasithin (Subgroup.centralizer ({t} : Set G)) :=
  isQuasithin_iff_twoLocal.mp h.quasithin _
    (Theory.GroupTheory.isTwoLocal_involution_centralizer ht)

theorem HasCharacteristicTwo.of_equiv (e : G ≃* H) (h : HasCharacteristicTwo G) :
    HasCharacteristicTwo H := by
  intro y hy
  have hx : e.symm y ∈ Subgroup.centralizer (pCore 2 G : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      hy (e x) (pCore_map_iso 2 e ▸ Subgroup.mem_map_of_mem e.toMonoidHom hx)
  have hh := Subgroup.mem_map_of_mem e.toMonoidHom (h hx)
  simpa only [pCore_map_iso, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hh

theorem HasCharacteristicTwo.equiv (e : G ≃* H) :
    HasCharacteristicTwo G ↔ HasCharacteristicTwo H :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

theorem IsEvenCharacteristicAt.map [Finite G] [Finite H] (e : G ≃* H) {T : Sylow 2 G}
    (h : IsEvenCharacteristicAt T) :
    IsEvenCharacteristicAt (T.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  intro M hM hTM
  have hle : (T : Subgroup G) ≤ M.map e.symm.toMonoidHom := by
    simpa [Sylow.coe_mapSurjective, Subgroup.map_map] using
      Subgroup.map_mono (f := e.symm.toMonoidHom) hTM
  exact (h (M.map e.symm.toMonoidHom)
    (Theory.GroupTheory.isMaximalTwoLocal_map e.symm hM) hle).of_equiv
    (Subgroup.equivMapOfInjective M e.symm.toMonoidHom e.symm.injective).symm

theorem IsEvenCharacteristicAt.all [Finite G] {T : Sylow 2 G}
    (h : IsEvenCharacteristicAt T) : IsEvenCharacteristic G := by
  intro S
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T S
  exact h.map (MulAut.conj g)

theorem isEvenCharacteristic_iff_at [Finite G] (T : Sylow 2 G) :
    IsEvenCharacteristic G ↔ IsEvenCharacteristicAt T :=
  ⟨fun h => h T, fun h => h.all⟩

theorem IsEvenCharacteristic.of_equiv [Finite G] [Finite H] (e : G ≃* H)
    (h : IsEvenCharacteristic G) : IsEvenCharacteristic H := by
  intro T
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective (f := e.toMonoidHom) e.surjective 2 T
  exact (h S).map e

theorem IsEvenCharacteristic.equiv [Finite G] [Finite H] (e : G ≃* H) :
    IsEvenCharacteristic G ↔ IsEvenCharacteristic H :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

theorem twoLocal_ne_top_of_nonabelian_simple [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {M : Subgroup G} (hM : IsTwoLocal M) : M ≠ ⊤ := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  intro hn
  have hnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hn
  have htop : Q = ⊤ := hnormal.eq_bot_or_eq_top.resolve_left hQ
  have hpG : IsPGroup 2 G := (htop ▸ hp).of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  have hcenter := hpG.bot_lt_center.ne'
  have hctop := (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top.resolve_left hcenter
  exact hna (Subgroup.center_eq_top_iff.mp hctop)

theorem IsSimpleQTKE.twoLocal_sqtk [Finite G] {K : GroupClass.{u}}
    (h : IsSimpleQTKE K G) {M : Subgroup G} (hM : IsTwoLocal M) : IsSQTK K M := by
  let := h.simple
  exact h.toIsQTKE.twoLocal_sqtk M hM (twoLocal_ne_top_of_nonabelian_simple h.nonabelian hM)

/-- Invariance required when specifying a group class using named models. -/
def GroupClass.IsIsoInvariant (K : GroupClass.{u}) : Prop :=
  ∀ (A B : Type u) [Group A] [Group B] (_e : A ≃* B), K A ↔ K B

theorem IsKGroup.mem {K : GroupClass.{u}} (h : IsKGroup K G) [IsSimpleGroup G] : K G :=
  h G inferInstance ⊤ Subgroup.topEquiv.toMonoidHom Subgroup.topEquiv.surjective

theorem IsKGroup.simple_quotient {K : GroupClass.{u}} (h : IsKGroup K G)
    (U : Subgroup G) (N : Subgroup U) [N.Normal] [IsSimpleGroup (U ⧸ N)] : K (U ⧸ N) :=
  h (U ⧸ N) inferInstance U (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- For an isomorphism-invariant class, the section formulation is equivalent
 to testing every simple quotient of every subgroup. -/
theorem isKGroup_iff_simple_quotients {K : GroupClass.{u}} (hK : K.IsIsoInvariant) :
    IsKGroup K G ↔ ∀ (U : Subgroup G) (N : Subgroup U) [N.Normal],
      IsSimpleGroup (U ⧸ N) → K (U ⧸ N) := by
  constructor
  · intro h U N _ hs
    let := hs
    exact h.simple_quotient U N
  · intro h S _ hs U f hf
    let := hs
    let e := QuotientGroup.quotientKerEquivOfSurjective f hf
    exact (hK _ _ e).mp (h U f.ker e.isSimpleGroup)

/-- K-groups are closed under extensions, because a simple section lies
 either in the normal subgroup or in the quotient. -/
theorem IsKGroup.of_normal_quotient {K : GroupClass.{u}} (N : Subgroup G) [N.Normal]
    (hN : IsKGroup K N) (hQ : IsKGroup K (G ⧸ N)) : IsKGroup K G := by
  intro S _ hs U f hf
  let := hs
  rcases Subgroup.simple_section_normal_or_quotient N U f hf with
    ⟨W, g, hg⟩ | ⟨W, g, hg⟩
  · exact hN S hs W g hg
  · exact hQ S hs W g hg

theorem IsKGroup.mono {K L : GroupClass.{u}}
    (hKL : ∀ (S : Type u) [Group S], K S → L S) (h : IsKGroup K G) : IsKGroup L G :=
  fun S _ hs U f hf => hKL S (h S hs U f hf)

theorem HasProperKSubgroups.of_equiv {K : GroupClass.{u}}
    (e : G ≃* H) (h : HasProperKSubgroups K G) : HasProperKSubgroups K H := by
  intro U hU
  have hp : U.map e.symm.toMonoidHom ≠ ⊤ := by
    intro ht
    have hh := congrArg (Subgroup.map e.toMonoidHom) ht
    apply hU
    simpa [Subgroup.map_map] using hh
  exact (h _ hp).of_injective
    (Subgroup.equivMapOfInjective U e.symm.toMonoidHom e.symm.injective).toMonoidHom
    (Subgroup.equivMapOfInjective U e.symm.toMonoidHom e.symm.injective).injective

theorem HasProperKSubgroups.equiv {K : GroupClass.{u}} (e : G ≃* H) :
    HasProperKSubgroups K G ↔ HasProperKSubgroups K H :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

theorem isSQTK_iff {K : GroupClass.{u}} :
    IsSQTK K G ↔ IsStronglyQuasithin G ∧ IsKGroup K G :=
  ⟨fun h => ⟨h.stronglyQuasithin, h.isKGroup⟩, fun h => ⟨h.1, h.2⟩⟩

theorem IsSQTK.equiv [Finite G] [Finite H] {K : GroupClass.{u}} (e : G ≃* H) :
    IsSQTK K G ↔ IsSQTK K H := by
  rw [isSQTK_iff, isSQTK_iff, IsStronglyQuasithin.equiv e, IsKGroup.equiv e]

theorem isQTKE_iff [Finite G] {K : GroupClass.{u}} :
    IsQTKE K G ↔ IsQuasithin G ∧ HasProperKSubgroups K G ∧ IsEvenCharacteristic G :=
  ⟨fun h => ⟨h.quasithin, h.properK, h.evenCharacteristic⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

theorem IsQTKE.of_equiv [Finite G] [Finite H] {K : GroupClass.{u}}
    (e : G ≃* H) (h : IsQTKE K G) : IsQTKE K H :=
  ⟨Theory.GroupTheory.isQuasithin_of_equiv e h.quasithin,
    h.properK.of_equiv e, h.evenCharacteristic.of_equiv e⟩

theorem IsQTKE.equiv [Finite G] [Finite H] {K : GroupClass.{u}} (e : G ≃* H) :
    IsQTKE K G ↔ IsQTKE K H :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

theorem IsSimpleQTKE.of_equiv [Finite G] [Finite H] {K : GroupClass.{u}}
    (e : G ≃* H) (h : IsSimpleQTKE K G) : IsSimpleQTKE K H := by
  let := h.simple
  refine ⟨h.toIsQTKE.of_equiv e, e.symm.isSimpleGroup, ?_⟩
  intro hc
  apply h.nonabelian
  rw [isMulCommutative_iff] at hc ⊢
  intro x y
  apply e.injective
  simpa only [map_mul] using hc (e x) (e y)

theorem IsSimpleQTKE.equiv [Finite G] [Finite H] {K : GroupClass.{u}} (e : G ≃* H) :
    IsSimpleQTKE K G ↔ IsSimpleQTKE K H :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

theorem IsSimpleQTKE.involution_centralizer_sqtk [Finite G] {K : GroupClass.{u}}
    (h : IsSimpleQTKE K G) {t : G} (ht : orderOf t = 2) :
    IsSQTK K (Subgroup.centralizer ({t} : Set G)) :=
  h.twoLocal_sqtk (Theory.GroupTheory.isTwoLocal_involution_centralizer ht)

end CFSG.Quasithin
