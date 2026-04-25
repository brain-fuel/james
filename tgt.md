# A Typed Graph Theory for Epistolary Text

This is Literate Idris2.

Fenced ` ```idris ` blocks are visible source compiled by the Idris 2 toolchain;

`<!-- idris ... -->` blocks are invisible source (compiled but not displayed);

everything else is prose.

Invoke with `idris2 --literate`.

<!-- idris
import Data.List
-->

```idris
module James
```


---


## Part I — Primitives


### Language

Root relations in `WordLexicalRelation` are language-tagged because
Greek and Hebrew roots behave differently: Greek compounds
productively, Hebrew roots are triconsonantal and pervasive.

```idris
public export
data Lang = Greek | Hebrew | Aramaic

export
Eq Lang where
  Greek   == Greek   = True
  Hebrew  == Hebrew  = True
  Aramaic == Aramaic = True
  _       == _       = False

export
Show Lang where
  show Greek   = "Greek"
  show Hebrew  = "Hebrew"
  show Aramaic = "Aramaic"
```


---


## Part II — The Semantic DAG

Nodes are propositional spans (verses or clauses). Edges are typed by
their rhetorical function. The inventory was derived by graphing James
1 and James 2 exhaustively; the set closed after two chapters.

```idris
public export
data VerseRelation
  = Entails
  | HooksOn
  | Contrasts
  | Elaborates
  | Grounds
  | Callback
  | Coordinate

export
Eq VerseRelation where
  Entails    == Entails    = True
  HooksOn    == HooksOn    = True
  Contrasts  == Contrasts  = True
  Elaborates == Elaborates = True
  Grounds    == Grounds    = True
  Callback   == Callback   = True
  Coordinate == Coordinate = True
  _          == _          = False

export
Show VerseRelation where
  show Entails    = "Entails"
  show HooksOn    = "HooksOn"
  show Contrasts  = "Contrasts"
  show Elaborates = "Elaborates"
  show Grounds    = "Grounds"
  show Callback   = "Callback"
  show Coordinate = "Coordinate"
```

**`Entails`** — B is the next logical step; removing it breaks the
inference. `1:2 → 1:3 → 1:4`; `1:14 → 1:15`; `2:2 → 2:3`.

**`HooksOn`** — B pivots on a word or root carried from A. Verbal, not
inferential. `1:4 → 1:5` on *λείπω*; `2:13 → 2:14` on *κρίσις*,
the structural seam between James 2's two halves.

**`Contrasts`** — B is the deliberate counter-pole of A; the tension is
the point. Directional because presentation order matters. `1:9 → 1:10`;
`2:5 → 2:6`; `2:18 → 2:19`.

**`Elaborates`** — B illustrates A without advancing the argument;
removal costs vividness only. `1:10 → 1:11`; `2:10 → 2:11`;
`2:14 → 2:15 → 2:16`.

**`Grounds`** — B answers *why* A holds, not *what comes next*. The
connective is causal: *γάρ*, *οὖν*. `1:19 → 1:20`; `2:9 → 2:10`;
`2:22 → 2:24`.

**`Callback`** — B refers backward to A across intervening material,
closing an inclusio or repeating a refrain. Drawn dashed; points
against reading direction. `1:4 → 1:12`; the triple *faith without
works is dead* at 2:17, 2:20, 2:26.

**`Coordinate`** — A and B are parallel siblings under a shared head,
not directly related. `1:26 ∥ 1:27`; Abraham and Rahab (`2:21 ∥ 2:25`).

The full set is enumerable:

```idris
export
allVerseRelations : List VerseRelation
allVerseRelations =
  [ Entails, HooksOn, Contrasts, Elaborates
  , Grounds, Callback, Coordinate
  ]

export
semanticCoversAll : List VerseRelation -> Bool
semanticCoversAll rs = all (`elem` rs) allVerseRelations
```

The correspondence to RST (Mann & Thompson, 1988) is close but
imperfect. `HooksOn` has no RST analogue: RST is purely semantic and
carries no record of surface lexical triggers. `Callback` is also
non-standard — RST is a tree, so backward cross-span reference
requires either node duplication or extension to a graph, which SDRT
(Asher & Lascarides, 2003) provides.


---


## Part III — The Lexical DAG

Nodes are lexemes (word tokens or types). Edges are typed by
word-level semantic relations. The inventory draws from WordNet
(Miller et al.) and Halliday & Hasan's lexical cohesion framework.

```idris
public export
data WordLexicalRelation
  = SameRoot Lang
  | Synonym
  | Antonym
  | Hyponym
  | Meronym
  | Reiteration
  | FrameEvocation

export
Eq WordLexicalRelation where
  SameRoot x     == SameRoot y     = x == y
  Synonym        == Synonym        = True
  Antonym        == Antonym        = True
  Hyponym        == Hyponym        = True
  Meronym        == Meronym        = True
  Reiteration    == Reiteration    = True
  FrameEvocation == FrameEvocation = True
  _              == _              = False

export
Show WordLexicalRelation where
  show (SameRoot l)   = "SameRoot " ++ show l
  show Synonym        = "Synonym"
  show Antonym        = "Antonym"
  show Hyponym        = "Hyponym"
  show Meronym        = "Meronym"
  show Reiteration    = "Reiteration"
  show FrameEvocation = "FrameEvocation"
```

**`SameRoot`** — same Greek or Hebrew root, possibly different surface
form. *πειρασμός* (1:2, trial) and *πειράζω* (1:13, to tempt) share
a root but carry opposite evaluative charge — precisely James's
rhetorical trap.

**`Synonym`** — different word, same sense in context.

**`Antonym`** — direct lexical opposition.

**`Hyponym`** — B is a kind of A.

**`Meronym`** — B is a part of A.

**`Reiteration`** — same word, same sense; deliberate repetition. The
*faith without works* refrain in James 2.

**`FrameEvocation`** — B evokes the same semantic frame as A without
sharing a root or sense. *νόμος*, *κριτής*, *κρίσις* all evoke
JUDGMENT.

The relation between the two DAGs is witnessed by `HooksOn`: every
`HooksOn` edge in the Semantic DAG requires at least one `SameRoot`,
`Reiteration`, or `FrameEvocation` edge in the Lexical DAG between
some word in span A and some word in span B. In Idris the predicate
is a type-level proof rather than a boolean assertion:

```idris
public export
data Witnesses : WordLexicalRelation -> VerseRelation -> Type where
  SameRootWitnesses : Witnesses (SameRoot l) HooksOn
  ReitWitnesses     : Witnesses Reiteration  HooksOn
  FrameWitnesses    : Witnesses FrameEvocation HooksOn
```

A `HooksOn` edge in the semantic graph can only be constructed if a
value of type `Witnesses lr HooksOn` is in scope — making the lexical
evidence a first-class inhabitant of the type rather than an assertion
in a comment.


---


## Part IV — Word Collections

Collections group lexemes by structural principle. Four kinds are
distinguished; each is a different *type* of collection.


### Lexical Chains

Theory basis: Morris & Hirst (1991); Barzilay & Elhadad (1997). A
chain is a sequence of lexemes across a text span held together by
word-level relations. Strength is *computed* from the relations
present, not asserted by constructor choice.

```idris
public export
record ChainLink a where
  constructor MkChainLink
  from     : a
  to       : a
  relation : WordLexicalRelation

public export
record Chain a where
  constructor MkChain
  links    : List (ChainLink a)
  textSpan : (Nat, Nat)

export
linkWeight : WordLexicalRelation -> Double
linkWeight r = case r of
  Reiteration    => 1.0
  SameRoot _     => 0.9
  Synonym        => 0.7
  Antonym        => 0.6
  Hyponym        => 0.5
  Meronym        => 0.4
  FrameEvocation => 0.4

export
strength : Chain a -> Double
strength (MkChain [] _) = 0.0
strength (MkChain ls _) =
  let weights = map (linkWeight . relation) ls
      total   = foldl (+) 0.0 weights
  in  total / cast (length weights)

export
isStrong : Chain a -> Bool
isStrong c = strength c >= 0.7
```

The JUDGMENT chain in James 2 is weak: all links are `FrameEvocation`,
scoring near 0.4. The *faith/works* chain is strong: repeated
`Reiteration` links score at 1.0.


### Semantic Fields

Theory basis: Trier (1931); Lyons (*Semantics*, 1977). A semantic
field is a set of lexemes clustering around a conceptual domain.
Fields are *closed* (exhaustive partition) or *open* (non-exhaustive).

```idris
public export
data FieldType = Closed | Open

public export
record SemanticField a where
  constructor MkSemanticField
  fieldType   : FieldType
  fieldDomain : String
  center      : List a
  periphery   : List a
```

The JUDGMENT field in James 2 is open: *νόμος*, *κριτής*, *κρίσις*,
*δίκαιος* cluster without exhausting the domain. Kinship terms are
the canonical closed field.


### Frame Participants

Theory basis: Fillmore (*Frame Semantics*, 1982); FrameNet. A frame is
a conceptual scenario evoked by a lexeme; participants are the roles
that scenario requires. Distinct from a semantic field: a field is
paradigmatic (substitution), a frame is syntagmatic (role-filling).

```idris
public export
data FrameRole = Core | NonCore

public export
record FrameParticipant a where
  constructor MkFrameParticipant
  participant : a
  role        : FrameRole
  roleName    : String

public export
record Frame a where
  constructor MkFrame
  frameLabel   : String
  evokedBy     : List a
  participants : List (FrameParticipant a)
```

The JUDGMENT frame in James 2 is evoked by *νόμος*, *κριτής*,
*κρίσις*. Core roles: Judge, Defendant, Verdict. Non-core: Law,
Penalty.


### Paradigmatic Sets

Theory basis: Saussure's associative relations; de Beaugrande &
Dressler (1981). A paradigmatic set is the set of lexemes licensed at
the same structural slot in a given context. The text's actual choice
is load-bearing precisely because the unchosen alternatives are
present as implicit contrast.

```idris
public export
record ParadigmaticSet a where
  constructor MkParadigmaticSet
  slotDescription : String
  slotContext     : String
  members         : List a
  chosen          : Maybe a
```

At James 1:5, the slot *[ask of X]* licenses {God, an elder, a wise
man, a teacher}. James chooses God; the others remain as rejected
alternatives framing the choice rhetorically.


### The Collection Type

```idris
public export
data WordCollection : Type -> Type where
  LexicalChain : Chain a           -> WordCollection a
  Field        : SemanticField a   -> WordCollection a
  FrameScene   : Frame a           -> WordCollection a
  Paradigmatic : ParadigmaticSet a -> WordCollection a
```


---


## Part V — Closed-set checks

```idris
export
allLexicalRelations : List WordLexicalRelation
allLexicalRelations =
  [ SameRoot Greek, SameRoot Hebrew, SameRoot Aramaic
  , Synonym, Antonym, Hyponym, Meronym, Reiteration, FrameEvocation
  ]

export
lexicalCoversAll : List WordLexicalRelation -> Bool
lexicalCoversAll rs = all (`elem` rs) allLexicalRelations
```
