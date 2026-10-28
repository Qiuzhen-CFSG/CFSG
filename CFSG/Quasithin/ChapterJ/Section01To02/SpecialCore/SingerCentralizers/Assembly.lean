module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Geometry
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.FullCentralizer
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Choice
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Singer choice and the centralizer clauses of J.2.3

Multiplication identifies C_S(s) with the internal direct product of the
fixed four-group and its Singer commutator factor. The exact model stabilizer
gives the full pointwise product in C_L(s) and the Sylow assertion. Cubic
invariance and the two actual Singer orbits complete the nonabelian Suzuki
argument, including derived subgroup equal to center. The intersection
argument supplies exact exponent four, rather than assuming it.

`source_singer_centralizers` constructs the Singer choice for the original
Sylow three-subgroup of O²(C_L(Z)). It proves J.2.3(1),(3)–(5) from LocalSetup,
the preceding J.2.1 conclusions |Z|=2 and Z≤V, and the independent full
commutator assertion J.2.3(6). The preceding parabolic development discharges
the first two inputs; the SpecialCore assembly discharges the last. No
Singer existence, module restriction, normalization or splitting premise remains.

Source: Aschbacher–Smith, Lemma J.2.3(1),(3)–(5), printed pp.433–434
(PDF pp.444–445), and Definition 2.4.13, printed p.532;
combined manuscript of 1 March 2004.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- J.2.3(4): the original cubic subgroup normalizes all three source subgroups. -/
theorem SingerChoice.centralizer_normalization (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    cubicSubgroup d B ≤ normalizer (d.S ⊓ centralizer ({s} : Set G) : Subgroup G) ∧
    cubicSubgroup d B ≤ normalizer (fixedCore d c.B7) ∧
    cubicSubgroup d B ≤ normalizer (movingCore d c.B7 s) := by
  have hn := c.cubic_normalizes_coreCentralizer d B hB hfull s hs hs1
  exact ⟨hn,c.normalizes_fixedCore d B,c.normalizes_movingCore d B s hn⟩

/-- The internal direct product in J.2.3(3), retaining multiplication and
both original factor embeddings. -/
theorem SingerChoice.coreCentralizer_internalProduct (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    ∃ e : fixedCore d c.B7 × movingCore d c.B7 s ≃*
        (d.S ⊓ centralizer ({s} : Set G) : Subgroup G),
      ∀ a m, (e (a,m) : G) = (a : G) * (m : G) := by
  have hn := (c.centralizer_normalization d B hB hfull s hs hs1).2.2
  have hc := c.movingCore_centralizes_fixedCore d B s hs hn
    (fun x hx hx1 => c.transitive_fixedCore d B hB s x hs hx hs1 hx1)
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (fixedCore d c.B7) (movingCore d c.B7 s)
    (c.fixedCore_disjoint_movingCore d B hB hfull s hs hs1)
    (le_centralizer_iff.mp hc)
  exact ⟨e.trans (MulEquiv.subgroupCongr
    (c.coreCentralizer_eq_sup_from_restriction d B s hs).symm),he⟩

/-- The literal pointwise product for the full centralizer in J.2.3(3). -/
theorem SingerChoice.fullCentralizer_product (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    (↑(d.L ⊓ centralizer ({s} : Set G)) : Set G) =
      (fixedCore d c.B7 : Set G) * (movingCore d c.B7 s : Set G) * (c.B7 : Set G) := by
  obtain ⟨e,he⟩ := c.coreCentralizer_internalProduct d B hB hfull s hs hs1
  have hCSL : d.S ⊓ centralizer ({s} : Set G) ≤ d.L ⊓ centralizer ({s} : Set G) :=
    inf_le_inf d.ru1.steinberg.section_le le_rfl
  have hF : fixedCore d c.B7 ≤ d.L ⊓ centralizer ({s} : Set G) := by
    apply le_trans _ hCSL
    rw [c.coreCentralizer_eq_sup_from_restriction d B s hs]
    exact le_sup_left
  have hM : movingCore d c.B7 s ≤ d.L ⊓ centralizer ({s} : Set G) := by
    apply le_trans _ hCSL
    rw [c.coreCentralizer_eq_sup_from_restriction d B s hs]
    exact le_sup_right
  have h7 : c.B7 ≤ d.L ⊓ centralizer ({s} : Set G) := by
    intro b hb
    exact ⟨c.le_L hb,mem_centralizer_singleton_iff.mpr (hs.2 b hb)⟩
  ext l
  constructor
  · intro hl
    obtain ⟨x,hx,b,hb,rfl⟩ := c.fullCentralizer_factor d B s hs hs1 l hl
    obtain ⟨⟨a,m⟩,ham⟩ := e.surjective ⟨x,hx⟩
    have heq : (a : G) * (m : G) = x :=
      (he a m).symm.trans (congrArg Subtype.val ham)
    exact Set.mem_mul.mpr ⟨x,Set.mem_mul.mpr ⟨a,a.property,m,m.property,heq⟩,b,hb,rfl⟩
  · rintro ⟨x,⟨a,ha,m,hm,rfl⟩,b,hb,rfl⟩
    exact (d.L ⊓ centralizer ({s} : Set G)).mul_mem
      ((d.L ⊓ centralizer ({s} : Set G)).mul_mem (hF ha) (hM hm)) (h7 hb)

/-- J.2.3(5), including the full definition of a Suzuki two-group:
nonabelianness, derived subgroup equal to center, and a cyclic group of actual
automorphisms transitive on all involutions. -/
theorem SingerChoice.movingCore_suzuki (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    IsPGroup 2 (movingCore d c.B7 s) ∧
    ¬ IsMulCommutative (movingCore d c.B7 s) ∧
    _root_.commutator (movingCore d c.B7 s) = center (movingCore d c.B7 s) ∧
    ∃ A : Subgroup (MulAut (movingCore d c.B7 s)), IsCyclic A ∧
      ∀ x y : movingCore d c.B7 s, orderOf x = 2 → orderOf y = 2 →
        ∃ a ∈ A, a x = y := by
  exact c.movingCore_suzuki_from_restriction d B hB hfull s hs hs1
    (c.centralizer_normalization d B hB hfull s hs hs1).2.2
    (c.transitive_movingCore_mod_V d B hB hfull s hs hs1)


/-- The Singer choice and J.2.3(1),(3)–(5) for the source LocalSetup.
The two J.2.1 premises are discharged by the preceding parabolic development;
the full-commutator premise is the independent J.2.3(6) theorem. Every Singer,
module, splitting, normalization, nonabelianness and exact-exponent premise
is discharged here. -/
theorem source_singer_centralizers (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hZ : Nat.card d.toTypeRuSetup.Z = 2) (hZV : d.toTypeRuSetup.Z ≤ d.V)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V) :
    let r := d.toTypeRuSetup
    ∃ c : SingerChoice r B,
      Nat.card (cubicSubgroup r B) = 3 ∧
      Nonempty (fixedCore r c.B7 ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
      ⁅fixedCore r c.B7, cubicSubgroup r B⁆ = fixedCore r c.B7 ∧
      ∀ s : G, s ∈ fixedCore r c.B7 → s ≠ 1 →
        (↑(r.L ⊓ centralizer ({s} : Set G)) : Set G) =
          (fixedCore r c.B7 : Set G) * (movingCore r c.B7 s : Set G) * (c.B7 : Set G) ∧
        (∃ e : fixedCore r c.B7 × movingCore r c.B7 s ≃*
            (r.S ⊓ centralizer ({s} : Set G) : Subgroup G),
          ∀ a m, (e (a,m) : G) = (a : G) * (m : G)) ∧
        (∃ P : Sylow 2 (r.L ⊓ centralizer ({s} : Set G) : Subgroup G),
          (P : Subgroup (r.L ⊓ centralizer ({s} : Set G) : Subgroup G)).map
            (r.L ⊓ centralizer ({s} : Set G) : Subgroup G).subtype =
              r.S ⊓ centralizer ({s} : Set G)) ∧
        Nat.card (r.S ⊓ centralizer ({s} : Set G) : Subgroup G) = 256 ∧
        Monoid.exponent (r.S ⊓ centralizer ({s} : Set G) : Subgroup G) = 4 ∧
        (cubicSubgroup r B ≤ normalizer (r.S ⊓ centralizer ({s} : Set G) : Subgroup G) ∧
          cubicSubgroup r B ≤ normalizer (fixedCore r c.B7) ∧
          cubicSubgroup r B ≤ normalizer (movingCore r c.B7 s)) ∧
        IsPGroup 2 (movingCore r c.B7 s) ∧
        ¬ IsMulCommutative (movingCore r c.B7 s) ∧
        _root_.commutator (movingCore r c.B7 s) = center (movingCore r c.B7 s) ∧
        ∃ A : Subgroup (MulAut (movingCore r c.B7 s)), IsCyclic A ∧
          ∀ x y : movingCore r c.B7 s, orderOf x = 2 → orderOf y = 2 →
            ∃ a ∈ A, a x = y := by
  let r := d.toTypeRuSetup
  have hB := cubicSubgroup_card r B hZ hZV
  obtain ⟨c⟩ := nonempty_singerChoice r B
  refine ⟨c,hB,⟨c.fixedCoreEquivFour r B⟩,c.fixedCore_commutator_cubic r B hB,?_⟩
  intro s hs hs1
  have ho := c.coreCentralizer_order_exponent_from_restriction r B hfull s hs hs1
  exact ⟨c.fullCentralizer_product r B hB hfull s hs hs1,
    c.coreCentralizer_internalProduct r B hB hfull s hs hs1,
    c.coreCentralizer_sylow r B s hs hs1,ho.1,ho.2,
    c.centralizer_normalization r B hB hfull s hs hs1,
    c.movingCore_suzuki r B hB hfull s hs hs1⟩

end CFSG.Quasithin.ChapterJ.SpecialCore
