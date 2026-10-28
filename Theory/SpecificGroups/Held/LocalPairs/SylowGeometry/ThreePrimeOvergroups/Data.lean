module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphData

/-!
# Data for a small orbit test in the concrete Held action

The eight words are elements of the exact ATLAS carrier. Their generated
subgroup and a candidate 24-part orbit labeling are used to reduce the
three-prime overgroup problem to a finite graph calculation. The data make
no assertion that the subgroup is a two-group or that the labels are orbits.
Those assertions, and the pair-stabilizer calculation, require separate proofs.

`Source/generate_data.py` reproduces this file from retained words and orbit
lists, checking their interpretation against HeG1-p2058B0. Sources: the literal
ATLAS generators in Held/Model/Source; GLS3 Table 5.3p; the missing Held-case
application on Aschbacher–Smith printed p.725. The graph is the existing
`Held.NormalizerGraph.Adj`, with its definition preserved.
-/

@[expose] public section

namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups

open Held.NormalizerGraph
open scoped Pointwise

/-- Eight literal words in the fixed Held generators. -/
def seedGenerator (i : Fin 8) : He :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 3 * a⁻¹ * b * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b * a⁻¹ * b * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 3 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b else (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a * (b) ^ 3 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b * a * (b) ^ 3 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b) ^ 2 * a⁻¹ * b * a⁻¹ * b * a * (b⁻¹) ^ 3 * a⁻¹ * (b⁻¹) ^ 2 * a * b * a⁻¹ * b⁻¹ * (a⁻¹) ^ 3 * (b⁻¹) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b * a * (b) ^ 2 * a * b * a⁻¹ * b⁻¹ * (a⁻¹) ^ 3 * (b⁻¹) ^ 5 * a⁻¹ * (b⁻¹) ^ 4 * a⁻¹ * b⁻¹) else (if i.val < 3 then a⁻¹ * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b * a * b * a * (b) ^ 2 * a * b * a * b⁻¹ * a * (b) ^ 2 * a * b⁻¹ * a * (b) ^ 2 * a * b * a⁻¹ * (b⁻¹) ^ 3 * a⁻¹ * (b⁻¹) ^ 3 * a⁻¹ * (b⁻¹) ^ 3 * a⁻¹ * b⁻¹ * a⁻¹ * (b) ^ 2 * a⁻¹ else (b) ^ 5 * a * b * a * b * a * (b) ^ 3 * a * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 3 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 3 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a * b * a * b * a * b * a * (b⁻¹) ^ 2 * a * (b) ^ 2 * a * b)) else (if i.val < 6 then (if i.val < 5 then b⁻¹ * a * (b⁻¹) ^ 2 * a * (b) ^ 2 * a * b⁻¹ * a * (b) ^ 2 * a * (b) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b) ^ 3 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b) ^ 3 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 3 * a⁻¹ * (b⁻¹) ^ 3 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 5 else a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a * (b) ^ 3 * a * (b⁻¹) ^ 2 * a * (b⁻¹) ^ 3 * a * b * a * (b⁻¹) ^ 2 * a * b * a * b⁻¹ * a * (b) ^ 2 * a * (b⁻¹) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a * b * a * (b) ^ 2 * a * b * a * (b) ^ 2 * a * b * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹) else (if i.val < 7 then a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ else (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a * (b) ^ 3 * a * b * a * (b⁻¹) ^ 3 * a * b * a * (b⁻¹) ^ 2 * a * (b) ^ 2 * a * (b⁻¹) ^ 2 * a * (b) ^ 2 * a * (b) ^ 2 * a * b * a * b⁻¹ * a * (b⁻¹) ^ 3 * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹) ^ 3 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a * b * a * b * a * (b⁻¹) ^ 3 * a⁻¹ * b * a * (b) ^ 2 * a * b * a⁻¹ * b⁻¹ * (a⁻¹) ^ 3 * (b⁻¹) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b * a * (b⁻¹) ^ 3 * a⁻¹ * (b⁻¹) ^ 2 * a * b * a⁻¹ * b⁻¹ * (a⁻¹) ^ 3 * (b⁻¹) ^ 2 * (a⁻¹) ^ 2 * (b) ^ 2 * a⁻¹ * (b⁻¹) ^ 2 * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹)))

/-- A concrete subgroup; its two-group property is a separate obligation. -/
def seedSubgroup : Subgroup He :=
  Subgroup.closure (Set.range seedGenerator)

/-- Candidate orbit labels, packed in five-bit fields. -/
def orbitLabel (x : Fin 2058) : ℕ :=
  (0x2d525af7a54b7bdacb959f7ade3565eed95536b96f14d2d1baaf565d158ca70bae2ab5a339deb78d6977d59745a36a5eb5ad6f53de937da75352b74ddb0adaf7b40cf3aad59aed45162db22e88de50bd875a56b7ab2eea3ed7a5ab6b4a75a2e08bdef795a84bcaf7a2236b4617bb6d14d2b1bca769b6cca2e508c6d665e974ded3bd917bd8f4595145bab77c957bde879bef0ad656bdab795e8cac257bdeb2b5e75ab2f6a3993a52f77da579daca526f593af5bd230a5654b5af6bced0bded5bce57955b4aa58fb21f784e57b5af66d977b5e3595a4da9a767ceb7bde4facaf75ca02bca779deb58d6918c6f7bd2eeaaef4bd21575c96b31d5adeecbb2564decd8ced5bc6b59ced7bddd5bcef5832f7bded285217ac1d37c1e885e7785ed4b51ed7bab2bd64cb5473baef1ac617b32b2aba3695dd22b2f1bb1f3bdd95adeb6bd1edbd6f1ad68fb42a5b5accba23735e778ca2ead653bd63795ad799dd7bc6f794e32bc6f7adad5bd95265cd7ad6f2bc6f55dd35b4ef7a4ad6b5677a5e9275ef78cecabdeea8daf5bca97bde36b56eeaded5bcaf7bb617bdaaebc6d2bd285b5d93adad7ad6d7749d7bc6b39ddb7ad6f564ed59da73aded5bb1b7b5ecc4ded795ef1bd01235a4cadef565e52b5aafb32f695cd7bded00c9523def64caf3b5aa279ad583aeb64a34ba935b3ad7456d1bd954bba3765aefa5d92bdef5656f2a36317ded6ad2b3756f17d2b765eaeb564f9c6259a217a591185eadbbad5a4a336ddb7bb6f26c6f6bde35946d195475bdab7a59b6926ca74ab5acef0ade86bb475b59eebc6cdaddcd55197b5cb7bdacf2d6b57bdf7ba6f4bd5717c5f665aed9de8b446f665626746b3b31afbd6f5ade158dd978ce979dd73aded6692b7a5af6bce77b5ad0ac2777def3b26771deeba2516b56d17cab4b3dd4adef5ba6f3a2157bddd7ade8bbc690836867deb58a5974daf79cef2a51f1bbef6bd6769cef7ac5b4b9e3762d94a95d685af28def7726f0bdc2c6bef3addf6b4ad4a5e17bd653bde57bde22addd7b45d3a56763daf5bd6d3845b2b3d71bdef4b5d57456b6652f4ad6ef9cef695ab7abaf7adef495df595db08de3695ecf85ef37d66eb5aeeb4aed6ae169ca2cb9e17bc6e8ac5b344ecd5b2f6a8ae8b46d0b54f1b518865cf4bdeb6bb9974deb5aca528d4b595675b38f4ad6f78de75bd6f295ef735ed11ce94a5af664e37bcdd6bd2f7a5156bd2959c6b3bd6f5b466ab5635746f1ba697a5ad7bdd37bd073ad60d45df535ef6bd6ecad6abbdd46bdef394ace6b2d2bc2a4aaab7a5ef4ace578ced1b4233bda36aaa95b5e75a56f77c6aa85ae9bb22d9d6e47ce1275af775a35b5a33bc2f76ce4675e144bab1bd995ade779565692952b5eec955ef9a9728b6f1956c7bd6777567744e57a4151041b75def65cef64da344daaeabef7bd4f7bb2308de31a5db4a5674b52b1bd6b0a4ef575551acef5ac2ee6dd776d6b3bc2f2b3a17659b7bbad78d2f495a2e7c995bcecf946e8bdeb7acaf7bc6f7b3637bb567bced2a4a958c9f77c6efbd2d78d234b5ed699532bdaf2b91d595af06deabbb1b6a5a4fa5ef6b36f6b5e9573676952b7bbad7a5ef7bc277b56ef9daf2a5eb724ad7bcced7d5f2a5cb5b5e93bda97956b5a4e776d6d77adf7949975de4e95ef4bb6f7b227495ab1bd62d6ded6b4875452f78ced05cab784197ada77bd2ceb54b5ba9d433af6ace969d676455929582e8b117bd6686a6166def06dad19a6f76deaab2636ba9949d6f79b553bd5f775ad7bbaf76d535ade77bdef2952d5b36280cee895a4c8d6e5 >>> (5 * x.val)) % 32

/-- A vertex in the candidate two-element orbit. -/
def basepoint : Fin 2058 := 447

/-- The candidate two-element orbit, using Lean's zero-based indices. -/
def basePair : Finset (Fin 2058) := {447, 1337}

/-- The actual setwise stabilizer in Held of the specified pair. -/
def pairStabilizer : Subgroup He :=
  MulAction.stabilizer He (basePair : Set (Fin 2058))

/-- Degree inside the induced relation on a finite set. -/
def neighborCount (U : Finset (Fin 2058)) (x : Fin 2058) : ℕ :=
  (U.filter (Adj x)).card

/-- Number of common neighbors inside the induced relation. -/
def commonCount (U : Finset (Fin 2058)) (x y : Fin 2058) : ℕ :=
  (U.filter fun z => Adj x z ∧ Adj y z).card

/-- Number of partners with exactly two common neighbors inside the set. -/
def profileCount (U : Finset (Fin 2058)) (x : Fin 2058) : ℕ :=
  (U.filter fun y => commonCount U x y = 2).card

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
