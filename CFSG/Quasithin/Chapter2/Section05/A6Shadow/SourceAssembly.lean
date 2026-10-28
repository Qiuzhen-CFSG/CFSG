module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Terminal
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction

/-!
# Source assembly for the terminal A₆ shadow

This extension connects the independent earlier-source interface to the
terminal construction.  The centralizer theorem below is deliberately stated
with the genuine data in `J = C_G(t)`: a normal A₆ factor, a Sylow subgroup of
`J`, the supplement from 2.5.18, characteristic two for `C_J(K)`, and the
actual conjugation action on `K`.  Thus `C_G(t) ≤ H` is proved before it is
used by the later construction.

The final contradiction theorem keeps the source-producing clauses explicit.
In particular, the Frattini/large-pair input, the concrete model adapters and
the central-intersection clause of 1.1.4(3) remain hypotheses for the section
assembly that owns them.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter2.A6Shadow.Frattini
open CFSG.Quasithin.Chapter2.A6ShadowConstruction

namespace CFSG.Quasithin.Chapter2.A6Shadow

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The genuine earlier-source centralizer reduction.  The subgroup `KJ` is
relative to `J = C_G(t)`, so the action used here is the actual conjugation
action, rather than an unmarked quotient isomorphism. -/
theorem centralizer_eq_of_source
    (d : EarlierSetup κ G)
    (KJ : Subgroup (centralizer ({d.t} : Set G))) [KJ.Normal]
    (eJ : KJ ≃* alternatingGroup (Fin 6))
    (SJ : Sylow 2 (centralizer ({d.t} : Set G)))
    (hH : d.H = (KJ ⊔ (SJ : Subgroup (centralizer ({d.t} : Set G)))).map
      (centralizer ({d.t} : Set G)).subtype)
    (hgen : KJ ⊔ (SJ : Subgroup (centralizer ({d.t} : Set G))) ⊔
      centralizer (KJ : Set (centralizer ({d.t} : Set G))) = ⊤)
    (hchar : centralizer (pCore 2 (centralizer (KJ : Set (centralizer ({d.t} : Set G)))) :
      Set (centralizer (KJ : Set (centralizer ({d.t} : Set G))))) ≤
      pCore 2 (centralizer (KJ : Set (centralizer ({d.t} : Set G)))))
    (hsurj : Function.Surjective
      (AlternatingSix.ShadowLocal.conjugationAction KJ eJ))
    (a : MulAut SJ)
    (hd : Disjoint
      ((centralizer (KJ : Set (centralizer ({d.t} : Set G)))).subgroupOf SJ)
      (((centralizer (KJ : Set (centralizer ({d.t} : Set G)))).subgroupOf SJ).map
        a.toMonoidHom)) :
    centralizer ({d.t} : Set G) = d.H := by
  exact (centralizer_eq_of_earlier_source d.simpleQTKE d.t d.t_order d.H KJ eJ SJ hH
    hgen hchar hsurj a hd).symm

/-- Transport the earlier source record into the exact setup consumed by the
terminal construction.  The two central subgroup conventions are bridged by
`centralizer_K`; no later conclusion is inserted into the record. -/
def toConstructionSetup
    (d : EarlierSetup κ G)
    (halternatives :
      Nonempty ((d.S ⊓ centralizer (d.K : Set G) : Subgroup G) ≃*
        Multiplicative (ZMod 4)) ∨
      Nonempty ((d.S ⊓ centralizer (d.K : Set G) : Subgroup G) ≃*
        Multiplicative (ZMod 8)) ∨
      Nonempty ((d.S ⊓ centralizer (d.K : Set G) : Subgroup G) ≃*
        QuaternionGroup 2))
    (hlargest : ∀ (E : Subgroup G), E ≤ d.S ⊓ d.K → IsKleinFour E →
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
        localPairs (Chapter1.He G) d.M ∧
      ∀ W ∈ localBases (Chapter1.He G) d.M,
        Nat.card W ≤ Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G))
    (hsylow : ∀ (E : Subgroup G), E ≤ d.S ⊓ d.K → IsKleinFour E →
      ∃ P : Sylow 2 (d.H ⊓ normalizer (E : Set G) : Subgroup G),
      (P : Subgroup (d.H ⊓ normalizer (E : Set G) : Subgroup G)).map
        (d.H ⊓ normalizer (E : Set G)).subtype =
        d.S ⊓ normalizer (E : Set G))
    (htx : d.x⁻¹ * d.t * d.x = d.zK)
    (hz : d.z = d.t * d.zK) :
    A6ShadowConstruction.Setup G := by
  let hcore : d.S ⊓ centralizer (d.K : Set G) = twoCore d.H :=
    d.centralizer_K.symm.trans d.core
  refine {
    H := d.H
    K := d.K
    S := d.S
    T := (d.T : Subgroup G)
    M := d.M
    generated := d.generated
    normalK := d.normalK
    modelK := d.modelK
    sylow := d.sylow
    sylow_eq := d.sylow_eq
    twoT := d.T.isPGroup'
    s_le_t := d.s_le_t
    x := d.x
    x_mem := d.x_mem
    x_normalizes := d.x_normalizes
    x_outside := d.x_outside
    square_mem := d.square_mem
    core_eq := hcore
    core_disjoint := by
      rw [← d.centralizer_K]
      exact d.disjoint_conjugate
    core_commutes := by
      rw [← d.centralizer_K]
      exact d.commuting_conjugate
    t := d.t
    zK := d.zK
    z := d.z
    t_mem := by
      rw [← d.centralizer_K]
      exact d.t_mem
    t_ne_one := by
      intro ht
      have ho := d.t_order
      rw [ht, orderOf_one] at ho
      norm_num at ho
    t_square := by
      have ho := pow_orderOf_eq_one d.t
      rw [d.t_order] at ho
      simpa only [pow_two] using ho
    center_s := by simpa only [centerIn_eq_map_center] using d.center_s
    center_sk := by simpa only [centerIn_eq_map_center] using d.center_sk
    t_conjugate := htx
    z_eq := hz
    action := d.action
    action_surjective := d.action_surjective
    action_compatible := d.action_compatible
    action_kernel := by
      rw [← d.centralizer_K]
      exact d.action_kernel
    alternatives := by
      exact halternatives
    largestPairs := by
      intro E hE hfour
      exact hlargest E hE hfour
    normalizerSylow := by
      intro E hE hfour
      exact hsylow E hE hfour }

/-- The construction retains the original ambient coordinates. This public
specification lets later source assemblies use the constructor while its
implementation remains private. -/
theorem toConstructionSetup_coordinates (d : EarlierSetup κ G) :
    ∀ halternatives hlargest hsylow htx hz,
      let q := toConstructionSetup d halternatives hlargest hsylow htx hz
      q.H = d.H ∧ q.M = d.M ∧ q.T = (d.T : Subgroup G) ∧
        q.t = d.t ∧ q.z = d.z := by
  intros
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Compose the source Frattini/involution conclusion with the terminal
construction.  The centralizer equality is supplied by
`centralizer_le_H_of_source`; all remaining displayed arguments are genuine
source/model clauses owned by the section assembly. -/
theorem false_of_source_assembly
    (d : EarlierSetup κ G)
    (KJ : Subgroup (centralizer ({d.t} : Set G))) [KJ.Normal]
    (eJ : KJ ≃* alternatingGroup (Fin 6))
    (SJ : Sylow 2 (centralizer ({d.t} : Set G)))
    (hH : d.H = (KJ ⊔ (SJ : Subgroup (centralizer ({d.t} : Set G)))).map
      (centralizer ({d.t} : Set G)).subtype)
    (hgen : KJ ⊔ (SJ : Subgroup (centralizer ({d.t} : Set G))) ⊔
      centralizer (KJ : Set (centralizer ({d.t} : Set G))) = ⊤)
    (hchar : centralizer (pCore 2 (centralizer (KJ : Set (centralizer ({d.t} : Set G)))) :
      Set (centralizer (KJ : Set (centralizer ({d.t} : Set G))))) ≤
      pCore 2 (centralizer (KJ : Set (centralizer ({d.t} : Set G)))))
    (hsurj : Function.Surjective
      (AlternatingSix.ShadowLocal.conjugationAction KJ eJ))
    (a : MulAut SJ)
    (hd : Disjoint
      ((centralizer (KJ : Set (centralizer ({d.t} : Set G)))).subgroupOf SJ)
      (((centralizer (KJ : Set (centralizer ({d.t} : Set G)))).subgroupOf SJ).map
        a.toMonoidHom))
    (hcor : d.EarlierPairCorrespondence)
    (halternatives :
      Nonempty ((d.S ⊓ centralizer (d.K : Set G) : Subgroup G) ≃*
        Multiplicative (ZMod 4)) ∨
      Nonempty ((d.S ⊓ centralizer (d.K : Set G) : Subgroup G) ≃*
        Multiplicative (ZMod 8)) ∨
      Nonempty ((d.S ⊓ centralizer (d.K : Set G) : Subgroup G) ≃*
        QuaternionGroup 2))
    (hlargest : ∀ (E : Subgroup G), E ≤ d.S ⊓ d.K → IsKleinFour E →
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
        localPairs (Chapter1.He G) d.M ∧
      ∀ W ∈ localBases (Chapter1.He G) d.M,
        Nat.card W ≤ Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G))
    (hsylow : ∀ (E : Subgroup G), E ≤ d.S ⊓ d.K → IsKleinFour E →
      ∃ P : Sylow 2 (d.H ⊓ normalizer (E : Set G) : Subgroup G),
      (P : Subgroup (d.H ⊓ normalizer (E : Set G) : Subgroup G)).map
        (d.H ⊓ normalizer (E : Set G)).subtype =
        d.S ⊓ normalizer (E : Set G))
    (htx : d.x⁻¹ * d.t * d.x = d.zK)
    (hz : d.z = d.t * d.zK)
    (q : A6ShadowConstruction.Setup G)
    (hq : q = toConstructionSetup d halternatives hlargest hsylow htx hz)
    (hcentral : ∀ (g : G), g⁻¹ * d.z * g ∈ d.S →
      (centralizer ({d.t} : Set G) ⊓
        centralizer ({g⁻¹ * d.z * g} : Set G)) ∈ Chapter1.He G)
    (hcharPair : ∀ (U L : Subgroup G),
      (U, L) ∈ localPairsIn (Chapter1.He G) d.M d.H →
        normalizer (twoCore L : Set G) ∈ Chapter1.He G)
    (h114 : ∀ A : Subgroup G, A ≠ ⊥ → IsPGroup 2 A →
      centerIn q.T ⊓ A ≠ ⊥ → A ∈ Chapter1.S2e G)
    (c : A6ShadowConstruction.CoreReduction.ModelGeometry
      (A6ShadowConstruction.CoreReduction.imageSylow q))
    (m : A6ShadowConstruction.SquareMembership.Fusion.ModelFacts)
    (n : A6ShadowConstruction.ActionNormalizer.ModelFacts)
    (o : A6ShadowConstruction.FourGroupChoice.ReflectionOrbit
      (A6ShadowConstruction.CoreReduction.imageSylow
        q)) : False := by
  have _hsource := source_frattini_and_involutions d hcentral hcor hcharPair
  subst q
  let q := toConstructionSetup d halternatives hlargest hsylow
    _hsource.2.1 _hsource.2.2
  have hC : centralizer ({d.t} : Set G) ≤ d.H := by
    exact (centralizer_eq_of_source d KJ eJ SJ hH hgen hchar hsurj a hd).le
  have hterm := q.exists_terminal_pair_of_source
    c m n o hC
  obtain ⟨V, s, E, e, h⟩ := hterm
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hAne, hAp, hzA, _, _, hIN, hpair, hmax, hUT, hxT, hxU, _, _, hsize⟩
  let y := q.x * (s : G)
  let A := E ⊔ conjugate y E
  have hstar : normalizer (A : Set G) ∈ gammaStar (Chapter1.He G) q.M :=
    normalizer_mem_gammaStar_of_crossing_element d.star
      q.sylow A q.T hAne hAp q.twoT
      hpair hmax (le_sup_left.trans hIN) hUT hxT.1 hxT.2 hxU hsize
  have hzT : d.z ∈ centerIn (d.T : Subgroup G) := by
    rw [d.center_t]
    exact mem_zpowers d.z
  have hinter : centerIn q.T ⊓ A ≠ ⊥ := by
    intro heq
    have ho := d.z_order
    have hz1 : d.z ≠ 1 := by
      intro hz1
      rw [hz1, orderOf_one] at ho
      norm_num at ho
    exact hz1 (show d.z ∈ (⊥ : Subgroup G) from heq ▸ ⟨hzT, hzA⟩)
  have hHe := (h114 A hAne hAp hinter).2.2
  have hmem : normalizer (A : Set G) ∈ gammaEvenZero (Chapter1.He G) q.M :=
    ⟨Or.inl hstar, hHe⟩
  have hempty : gammaEvenZero (Chapter1.He G) q.M = ∅ := by
    change gammaEvenZero (Chapter1.He G) d.M = ∅
    exact d.even_empty
  rw [hempty] at hmem
  exact hmem

end CFSG.Quasithin.Chapter2.A6Shadow
