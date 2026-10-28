module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.A8Reduction.ExtensionControl
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.A8Reduction.MarkedExtension
public import Theory.SpecificGroups.SymmetricEight.TranspositionAutomorphisms
public import Theory.SpecificGroups.SymmetricEight.TranspositionCentralizer

/-!
# Dihedral reduction in the exceptional A₈ branch

The conjugate SCˣ lies in Ki C_S(i) and centralizes t. Under the compatible
C₂ × S₈ identification, a two-element in the centralizer of the marked
transposition has fourth power one. Injectivity of conjugation gives this
identity in SC. Suzuki recognition, together with the source centralizer
identity and nontrivial Frattini subgroup, now gives SC ≃ D₈. The quotient
Sylow order 32 yields |S| = 256. The characteristic cyclic four of SC is
normalized by H = C_G(t), with its generator squaring to t.

The marked construction in `MarkedExtension` identifies the actual
H₀ = ⟨Ki,i,t⟩ with C₂ × S₈, preserving Ki, i and t. The intrinsic A₈
automorphism theorem discharges the lifting premise in `ExtensionControl`,
so C_S(i) ≤ H₀ and H₀ = Ki C_S(i). No extension or automorphism-lifting
premise remains in `dihedral_and_cyclicFour_of_localData`.

Source: Aschbacher–Smith, Lemma 2.5.26, printed pp.568–569, combined
1 March 2004 manuscript. `hquot` is the incoming Aut(A₆) quotient-Sylow
order. `exceptional_branch_reduction` also assembles relative normality
and Sylow placement outside Mᵍ, using precisely the involution-centralizer
consequence of source 1.1.3(2) as an earlier input. The subsequent fusion,
two-overgroup geometry and contradiction proving the component claim stay
with the parent assembly; this module does not assert all of Lemma 2.5.26.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Transport the finite-model power bound through the actual conjugate-core embedding. -/
theorem core_fourth_power_of_extension (d : LocalData G) (m : ExtensionModel d)
    (hmodel : ∀ a : SymmetricExtension,
      Commute a (1, Equiv.swap (0 : Fin 8) 1) →
      (∃ n : ℕ, orderOf a = 2 ^ n) → a ^ 4 = 1) : ∀ a : d.SC, a ^ 4 = 1 := by
  let f : d.SC →* d.extension :=
    (((MulAut.conj d.x).toMonoidHom.comp d.SC.subtype).codRestrict d.extension
      (fun a => d.conjugate_core_le_extension (mem_map_of_mem _ a.property)))
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact (MulAut.conj d.x).injective (congrArg Subtype.val hab)
  let tJ : d.extension := ⟨d.t, d.t_mem_extension⟩
  have htJ : m.equiv tJ = (1, Equiv.swap (0 : Fin 8) 1) := m.map_t tJ rfl
  intro a
  have haS : ((f a : d.extension) : G) ∈ d.S :=
    d.conjugate_core_le_s (mem_map_of_mem _ a.property)
  have hcomm : Commute (f a) tJ := by
    apply Subtype.ext
    exact d.t_central _ haS
  have himage : (m.equiv (f a)) ^ 4 = 1 := by
    apply hmodel
    · rw [← htJ]
      exact hcomm.map m.equiv.toMonoidHom
    · obtain ⟨n, hn⟩ := d.core_isPGroup.exists_orderOf_eq_pow a
      exact ⟨n, (m.equiv.orderOf_eq _).trans ((orderOf_injective f hf a).trans hn)⟩
  apply hf
  apply m.equiv.injective
  simpa only [map_pow, map_one] using himage

/-- The algebraic reduction with an explicit power bound. The bound is discharged
by `dihedral_and_cyclicFour` below; the extension must still be constructed. -/
theorem dihedral_and_cyclicFour_of_extension (d : LocalData G) (m : ExtensionModel d)
    (hmodel : ∀ a : SymmetricExtension,
      Commute a (1, Equiv.swap (0 : Fin 8) 1) →
      (∃ n : ℕ, orderOf a = 2 ^ n) → a ^ 4 = 1)
    (hquot : (d.SC.subgroupOf d.S).index = 32) :
    Nonempty (d.SC ≃* DihedralGroup 4) ∧ Nat.card d.S = 256 ∧
      ∃ V : Subgroup G, ∃ v : G, V ≤ d.SC ∧ V = zpowers v ∧ orderOf v = 4 ∧
        v ^ 2 = d.t ∧ centralizer ({d.t} : Set G) ≤ normalizer (V : Set G) := by
  obtain ⟨e⟩ := dihedral_of_involution_centralizer d.core_isPGroup
    (⟨d.i, d.i_mem⟩ : d.SC) (⟨d.t, d.t_mem⟩ : d.SC)
    (by simpa using d.i_order) (by simpa using d.t_order)
    (fun he => d.i_ne_t (congrArg Subtype.val he)) d.t_mem_center_core
    d.centralizer_i d.frattini_ne (core_fourth_power_of_extension d m hmodel)
  refine ⟨⟨e⟩, ?_, ?_⟩
  · have hc : Nat.card d.SC = 8 := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
    have hsc : Nat.card (d.SC.subgroupOf d.S) = 8 :=
      (Nat.card_congr (subgroupOfEquivOfLe d.core_le_s).toEquiv).trans hc
    have hh := (d.SC.subgroupOf d.S).index_mul_card
    simpa only [hquot, hsc] using hh.symm
  · obtain ⟨V, v, hVD, hV, hv, ht, hn⟩ := cyclicFour_of_dihedral d.SC e
      d.t d.t_mem d.t_order d.t_mem_center_core
    exact ⟨V, v, hVD, hV, hv, ht, d.centralizer_t ▸ d.core_normalizer.trans hn⟩

/-- The proved transposition calculation gives the source dihedral and cyclic-four
conclusions from the compatible extension and the Aut(A₆) Sylow order. -/
theorem dihedral_and_cyclicFour (d : LocalData G) (m : ExtensionModel d)
    (hquot : (d.SC.subgroupOf d.S).index = 32) :
    Nonempty (d.SC ≃* DihedralGroup 4) ∧ Nat.card d.S = 256 ∧
      ∃ V : Subgroup G, ∃ v : G, V ≤ d.SC ∧ V = zpowers v ∧ orderOf v = 4 ∧
        v ^ 2 = d.t ∧ centralizer ({d.t} : Set G) ≤ normalizer (V : Set G) :=
  dihedral_and_cyclicFour_of_extension d m
    Theory.SpecificGroups.SymmetricEight.product_transpositionCentralizer_fourth_power hquot

/-- Assembly interface for the two independent extension prerequisites. Neither
the marked carrier nor the centralizer containment is part of `LocalData`. -/
theorem dihedral_and_cyclicFour_of_smallExtension (d : LocalData G)
    (m : SmallExtensionModel d)
    (hCS : d.S ⊓ centralizer {d.i} ≤ d.smallExtension)
    (hquot : (d.SC.subgroupOf d.S).index = 32) :
    Nonempty (d.SC ≃* DihedralGroup 4) ∧ Nat.card d.S = 256 ∧
      ∃ V : Subgroup G, ∃ v : G, V ≤ d.SC ∧ V = zpowers v ∧ orderOf v = 4 ∧
        v ^ 2 = d.t ∧ centralizer ({d.t} : Set G) ≤ normalizer (V : Set G) :=
  dihedral_and_cyclicFour d
    (ExtensionModel.ofSmall m (d.smallExtension_eq_extension_of_centralizer_le hCS)) hquot

/-- After the two independent model constructions, the complete dihedral and
cyclic-four reduction uses only the permitted Aut(A₆) quotient order input. -/
theorem dihedral_and_cyclicFour_of_transposition_lifting (d : LocalData G)
    (hG : IsQuasithin G) (m : SmallExtensionModel d)
    (hlift : ∀ f : MulAut (alternatingGroup (Fin 8)),
      Commute f (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1)) →
      ∃ q : Equiv.Perm (Fin 8), Commute q (Equiv.swap (0 : Fin 8) 1) ∧
        MulAut.conjNormal q = f)
    (hquot : (d.SC.subgroupOf d.S).index = 32) :
    Nonempty (d.SC ≃* DihedralGroup 4) ∧ Nat.card d.S = 256 ∧
      ∃ V : Subgroup G, ∃ v : G, V ≤ d.SC ∧ V = zpowers v ∧ orderOf v = 4 ∧
        v ^ 2 = d.t ∧ centralizer ({d.t} : Set G) ≤ normalizer (V : Set G) :=
  dihedral_and_cyclicFour_of_smallExtension d m
    (centralizer_le_smallExtension_of_lifting d hG m hlift) hquot

/-- The actual marked carrier and the proved A₈ lifting theorem put all of
C_S(i) in H₀, with no additional extension premise. -/
theorem centralizer_le_smallExtension (d : LocalData G) (hG : IsQuasithin G) :
    d.S ⊓ centralizer {d.i} ≤ d.smallExtension := by
  obtain ⟨m⟩ := d.smallExtensionModel_nonempty
  exact centralizer_le_smallExtension_of_lifting d hG m
    Theory.SpecificGroups.SymmetricEight.lift_transpositionCentralizing_automorphism

/-- Construct Ki C_S(i) ≃ C₂ × S₈, retaining the marked images of Ki, i and t
and the equality Ki C_S(i) = ⟨Ki,i,t⟩. -/
theorem LocalData.extensionModel_nonempty (d : LocalData G) (hG : IsQuasithin G) :
    Nonempty (ExtensionModel d) := by
  obtain ⟨m⟩ := d.smallExtensionModel_nonempty
  exact ⟨ExtensionModel.ofSmall m
    (d.smallExtension_eq_extension_of_centralizer_le (centralizer_le_smallExtension d hG))⟩

/-- The first exceptional-branch reduction of 2.5.26: SC ≃ D₈, |S| = 256,
and the characteristic cyclic four normalized by C_G(t). All symmetric-group
model premises have been discharged; only the earlier local data and the
Aut(A₆) quotient-Sylow order enter. -/
theorem dihedral_and_cyclicFour_of_localData (d : LocalData G)
    (hG : IsQuasithin G) (hquot : (d.SC.subgroupOf d.S).index = 32) :
    Nonempty (d.SC ≃* DihedralGroup 4) ∧ Nat.card d.S = 256 ∧
      ∃ V : Subgroup G, ∃ v : G, V ≤ d.SC ∧ V = zpowers v ∧ orderOf v = 4 ∧
        v ^ 2 = d.t ∧ centralizer ({d.t} : Set G) ≤ normalizer (V : Set G) := by
  obtain ⟨m⟩ := d.extensionModel_nonempty hG
  exact dihedral_and_cyclicFour d m hquot

/-- Assemble the exceptional-branch outputs for the parent fusion and geometry
arguments. Here `h113` is exactly the involution-centralizer consequence of
1.1.3(2) for the conjugates of M. The models, relative normality, dihedral
shape, cyclic four, and outside-M condition are conclusions. -/
theorem exceptional_branch_reduction (d : LocalData G) (hG : IsQuasithin G)
    (hquot : (d.SC.subgroupOf d.S).index = 32) (T : Sylow 2 G) (M : Subgroup G)
    (h113 : ∀ (g j : G), j ∈ M.map (MulAut.conj g).toMonoidHom → orderOf j = 2 →
      M.map (MulAut.conj g).toMonoidHom ⊓ centralizer ({j} : Set G) ∈
        CFSG.Quasithin.Chapter1.He G) :
    Nonempty (SmallExtensionModel d) ∧ d.smallExtension = d.extension ∧
      centralizer ({d.i} : Set G) ≤ normalizer (d.Ki : Set G) ∧
      Nonempty (d.SC ≃* DihedralGroup 4) ∧ Nat.card d.S = 256 ∧
      (∃ V : Subgroup G, ∃ v : G, V ≤ d.SC ∧ V = zpowers v ∧ orderOf v = 4 ∧
        v ^ 2 = d.t ∧ centralizer ({d.t} : Set G) ≤ normalizer (V : Set G)) ∧
      ∀ U : Sylow 2 d.smallExtension,
        ∃ g : G, (U : Subgroup d.smallExtension).map d.smallExtension.subtype ≤
          (T : Subgroup G).map (MulAut.conj g).toMonoidHom ∧
          ¬ d.smallExtension ≤ M.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hD, hS, hV⟩ := dihedral_and_cyclicFour_of_localData d hG hquot
  exact ⟨d.smallExtensionModel_nonempty,
    d.smallExtension_eq_extension_of_centralizer_le (centralizer_le_smallExtension d hG),
    d.Ki_normalizer hG, hD, hS, hV,
    fun U => d.smallExtension_sylow_placement_outside hG T M U h113⟩

end CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction
