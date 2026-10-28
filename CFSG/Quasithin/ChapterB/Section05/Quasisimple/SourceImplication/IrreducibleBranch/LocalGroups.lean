module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Quasithin.Rank

/-!
# Local groups in the opening of B.5.1

If F*(G) = L Z(G), O₂(G) = 1 and L is quasisimple, every two-subgroup
acts faithfully on L. For each such subgroup A, the literal overgroup LA
has trivial two-core and generalized Fitting subgroup L. Strong quasithinness
passes from L to LA because every odd-prime subgroup has trivial image in
LA/L. The K-group argument uses only membership of simple two-groups in K.

Observation α follows by conjugating every offender into the chosen Sylow
subgroup. For β, an abelian Out(L) puts G' in L Z(G); hence G/L is nilpotent.
Its two-subgroups all lie in its unique Sylow two-subgroup. Offender generation
then implies G = LT for every ambient Sylow two-subgroup T.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of B.5.1,
printed p.99. These are the preliminary group reductions, independently of
the B.4.2 action catalogue and its triple-cover offender convention.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Centralizing L is equivalent to centralizing F*(G) in the source setup. -/
theorem centralizer_fitting_eq (L : Subgroup G)
    (hf : generalizedFitting G = L ⊔ center G) :
    centralizer (generalizedFitting G : Set G) = centralizer (L : Set G) := by
  rw [hf]
  apply le_antisymm (centralizer_le (show (L : Set G) ⊆ (L ⊔ center G : Subgroup G) from
    fun _ hx => (le_sup_left : L ≤ L ⊔ center G) hx))
  intro g hg
  have hL : L ≤ centralizer ({g} : Set G) := by
    intro l hl
    simpa only [mem_centralizer_singleton_iff] using (hg l hl)
  have hZ : center G ≤ centralizer ({g} : Set G) := by
    intro z hz
    simpa only [mem_centralizer_singleton_iff] using (mem_center_iff.mp hz g).symm
  intro x hx
  exact ((sup_le hL hZ) hx g (Set.mem_singleton g)).symm

/-- No nonidentity element of a two-subgroup centralizes L. -/
theorem twoSubgroup_disjoint_centralizer (L A : Subgroup G)
    (hf : generalizedFitting G = L ⊔ center G)
    (hcore : pCore 2 G = ⊥) (hA : IsPGroup 2 A) :
    Disjoint A (centralizer (L : Set G)) := by
  rw [← centralizer_fitting_eq L hf]
  exact QuasisimpleSections.disjoint_centralizer_fitting hcore A hA

/-- The restriction of the actual conjugation homomorphism is faithful. -/
theorem twoSubgroup_conjugation_injective (L A : Subgroup G) [L.Normal]
    (hf : generalizedFitting G = L ⊔ center G)
    (hcore : pCore 2 G = ⊥) (hA : IsPGroup 2 A) :
    Function.Injective ((MulAut.conjNormal : G →* MulAut L).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  apply Subtype.ext
  have hc : (a : G) ∈ centralizer (L : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer L]
    exact ha
  exact Subgroup.disjoint_def.mp (twoSubgroup_disjoint_centralizer L A hf hcore hA)
    a.property hc

/-- Every overgroup of L inherits the trivial two-core. -/
theorem local_twoCore_eq_bot (L D : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hf : generalizedFitting G = L ⊔ center G) (hcore : pCore 2 G = ⊥)
    (hLD : L ≤ D) : pCore 2 D = ⊥ := by
  have hcomp : IsComponent D (L.subgroupOf D) :=
    (show IsComponent G L from ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩).subgroupOf hLD
  let : IsQuasisimple (L.subgroupOf D) := hcomp.2
  rcases hcomp.normal_dichotomy (pCore 2 D) with hle | hc
  · let : IsSimpleGroup ((L.subgroupOf D) ⧸ center (L.subgroupOf D)) := IsQuasisimple.simple
    let : Nontrivial (L.subgroupOf D) :=
      (QuotientGroup.mk'_surjective (center (L.subgroupOf D))).nontrivial
    let : Group.IsNilpotent (L.subgroupOf D) := (pCore_isPGroup.to_le hle).isNilpotent
    exact (Group.IsPerfect.not_isSolvable (L.subgroupOf D) inferInstance).elim
  · have hC : (pCore 2 D).map D.subtype ≤ centralizer (L : Set G) := by
      rintro _ ⟨a, ha, rfl⟩ l hl
      have hh := commutator_eq_bot_iff_le_centralizer.mp hc
        (show (⟨l, hLD hl⟩ : D) ∈ L.subgroupOf D from hl) a ha
      exact (congrArg Subtype.val hh).symm
    have he : (pCore 2 D).map D.subtype = ⊥ :=
      (twoSubgroup_disjoint_centralizer L _ hf hcore
        (pCore_isPGroup.map D.subtype)).eq_bot_of_le hC
    exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp he

omit [Finite G] in
/-- The literal quotient LA/L is a two-group. -/
theorem local_quotient_isTwoGroup (L A : Subgroup G) [L.Normal]
    (hA : IsPGroup 2 A) :
    IsPGroup 2 (↥(L ⊔ A) ⧸ L.subgroupOf (L ⊔ A)) := by
  apply isPGroup_quotient_of_sup_eq_top (L.subgroupOf (L ⊔ A))
    (A.subgroupOf (L ⊔ A)) hA.comap_subtype
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]

/-- Relative Fitting identification inside LA. -/
theorem local_generalizedFitting (L A : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hf : generalizedFitting G = L ⊔ center G) (hcore : pCore 2 G = ⊥)
    (hA : IsPGroup 2 A) :
    generalizedFitting ↥(L ⊔ A) = L.subgroupOf (L ⊔ A) := by
  let : IsQuasisimple (L.subgroupOf (L ⊔ A)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left)).symm
  exact generalizedFitting_eq_of_quasisimple_two_quotient _
    (local_quotient_isTwoGroup L A hA)
    (local_twoCore_eq_bot L (L ⊔ A) hf hcore le_sup_left)

/-- The relative identification maps back to the original embedded L. -/
theorem local_generalizedFitting_map (L A : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hf : generalizedFitting G = L ⊔ center G) (hcore : pCore 2 G = ⊥)
    (hA : IsPGroup 2 A) :
    (generalizedFitting ↥(L ⊔ A)).map (L ⊔ A).subtype = L := by
  rw [local_generalizedFitting L A hf hcore hA]
  exact map_subgroupOf_eq_of_le le_sup_left


/-- Only the simple two-groups need to be added to K when adjoining a two-subgroup. -/
def ContainsSimpleTwoGroups (K : GroupClass.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], IsPGroup 2 S → K S

omit [Finite G] in
/-- Two-groups are K-groups under the exact class condition used here. -/
theorem isKGroup_of_isTwoGroup {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} (hK : ContainsSimpleTwoGroups K) (hp : IsPGroup 2 D) :
    IsKGroup K D := by
  intro S _ hs U f hf
  let : Finite S := Finite.of_surjective f hf
  let := hs
  exact hK S ((hp.to_subgroup U).of_surjective f hf)

/-- Odd-prime ranks do not increase on taking a two-group extension. -/
theorem stronglyQuasithin_of_twoGroup_quotient (L : Subgroup G) [L.Normal]
    (hq : IsPGroup 2 (G ⧸ L)) (hL : IsStronglyQuasithin L) :
    IsStronglyQuasithin G := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  apply (primeRank_le_iff p 2).mpr
  intro A hA hAc
  have he : A.map (QuotientGroup.mk' L) = ⊥ := by
    have hdis := (hA.map (QuotientGroup.mk' L)).disjoint_of_coprime
      (hq.to_subgroup (A.map (QuotientGroup.mk' L))) (Nat.coprime_two_right.mpr ho)
    simpa using hdis.eq_bot
  have hAL : A ≤ L := by
    simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using he
  have heq := Group.rank_congr (subgroupOfEquivOfLe hAL)
  rw [← heq]
  let := hAc
  exact (primeRank_le_iff p 2).mp (hL p hp ho) (A.subgroupOf L)
    hA.comap_subtype inferInstance

/-- Combine odd-prime rank and simple-section inheritance. -/
theorem sqtk_of_twoGroup_quotient {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} (hK : ContainsSimpleTwoGroups K) (L : Subgroup D) [L.Normal]
    (hq : IsPGroup 2 (D ⧸ L)) (hL : IsSQTK K L) : IsSQTK K D :=
  ⟨stronglyQuasithin_of_twoGroup_quotient L hq hL.stronglyQuasithin,
    IsKGroup.of_normal_quotient L hL.isKGroup (isKGroup_of_isTwoGroup hK hq)⟩

/-- The source groups LA are SQTK, with L embedded by subgroupOf. -/
theorem local_sqtk {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} (hK : ContainsSimpleTwoGroups K) (L A : Subgroup D) [L.Normal]
    (hL : IsSQTK K L) (hA : IsPGroup 2 A) : IsSQTK K ↥(L ⊔ A) := by
  exact sqtk_of_twoGroup_quotient hK (L.subgroupOf (L ⊔ A))
    (local_quotient_isTwoGroup L A hA)
    ((IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left))).mpr hL)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Source observation α: controlling the offenders in one Sylow subgroup suffices. -/
theorem whole_of_sylow_offenders_le (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hgen : offenderSubgroup ρ = ⊤)
    (hJT : generatedBy {A | IsBestOffender ρ A} T ≤ L) : L = ⊤ := by
  apply top_unique
  rw [← hgen]
  unfold offenderSubgroup generatedBy
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA, _⟩
  let := hA.1.2
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
  have hPT : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = T :=
    congrArg Sylow.toSubgroup hg
  have hAT : A.map (MulAut.conj g).toMonoidHom ≤ T :=
    hPT ▸ Subgroup.map_mono hAP
  have hc : A.map (MulAut.conj g).toMonoidHom ≤ L := by
    apply le_trans _ hJT
    unfold generatedBy
    exact le_iSup_of_le _ (le_iSup_of_le ⟨hA.map_conj ρ g, hAT⟩ le_rfl)
  intro a ha
  have hh := hc (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
  have hi := (inferInstance : L.Normal).conj_mem _ hh g⁻¹
  simpa [MulAut.conj_apply, mul_assoc] using hi


/-- An abelian outer group makes the ambient commutator central modulo L. -/
theorem commutator_le_component_sup_center (L : Subgroup G) [L.Normal]
    (hf : generalizedFitting G = L ⊔ center G) [IsMulCommutative (MulAut.Outer L)] :
    _root_.commutator G ≤ L ⊔ center G := by
  let f : G →* MulAut.Outer L :=
    (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp MulAut.conjNormal
  have hk : f.ker = L ⊔ centralizer (L : Set G) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', MulAut.conjNormal_comap_innerSubgroup]
  have hc : _root_.commutator G ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    apply le_bot_iff.mp
    rw [map_commutator_eq]
    exact (Subgroup.commutator_mono le_top le_top).trans_eq
      (show ⁅(⊤ : Subgroup (MulAut.Outer L)), ⊤⁆ = ⊥ from commutator_eq_bot (MulAut.Outer L))
  rw [hk] at hc
  apply hc.trans
  apply sup_le le_sup_left
  rw [← hf, ← centralizer_fitting_eq L hf]
  exact QuasisimpleSections.centralizer_generalizedFitting_le

/-- The outer-abelian case has a nilpotent quotient by L, before using offenders. -/
theorem quotient_nilpotent_of_outer_abelian (L : Subgroup G) [L.Normal]
    (hf : generalizedFitting G = L ⊔ center G) [IsMulCommutative (MulAut.Outer L)] :
    Group.IsNilpotent (G ⧸ L) := by
  let q := QuotientGroup.mk' L
  have hz : (center G).map q ≤ center (G ⧸ L) := by
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective L x
    simpa only [map_mul] using congrArg q ((mem_center_iff.mp hz) g)
  have hc : _root_.commutator (G ⧸ L) ≤ center (G ⧸ L) := by
    have hm := Subgroup.map_mono (f := q) (commutator_le_component_sup_center L hf)
    rw [Subgroup.map_sup, show L.map q = ⊥ from (Subgroup.map_eq_bot_iff _).mpr (by simp [q]),
      bot_sup_eq] at hm
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective L)] at hm
    exact hm.trans hz
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨2, Subgroup.lowerCentralSeries_succ_eq_bot ⊤ ?_⟩
  simpa only [top_lowerCentralSeries_one] using hc

/-- Source observation β, on the actual outer group and each ambient Sylow subgroup. -/
theorem whole_eq_component_sylow_of_outer_abelian (L : Subgroup G) [L.Normal]
    (hf : generalizedFitting G = L ⊔ center G)
    [IsMulCommutative (MulAut.Outer L)] (hgen : offenderSubgroup ρ = ⊤)
    (T : Sylow 2 G) : L ⊔ (T : Subgroup G) = ⊤ := by
  let q := QuotientGroup.mk' L
  let : Group.IsNilpotent (G ⧸ L) := quotient_nilpotent_of_outer_abelian L hf
  let P : Sylow 2 (G ⧸ L) := T.mapSurjective (QuotientGroup.mk'_surjective L)
  have hle : ⊤ ≤ (P : Subgroup (G ⧸ L)).comap q := by
    rw [← hgen]
    unfold offenderSubgroup generatedBy
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩
    apply Subgroup.map_le_iff_le_comap.mp
    let := hA.1.2
    have hp := (IsElementaryAbelian.isPGroup 2 A).map q
    have hs := P.is_maximal' (hp.to_sup_of_normal_right P.isPGroup') le_sup_right
    exact (le_sup_left : A.map q ≤ A.map q ⊔ (P : Subgroup (G ⧸ L))).trans_eq hs
  have he := top_unique hle
  change ((T : Subgroup G).map q).comap q = ⊤ at he
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at he
  simpa only [sup_comm] using he

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
