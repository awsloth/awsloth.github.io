import markdown2
import shutil
import os

send_dir = "_site"

markdowner = markdown2.Markdown()

ls_dir = os.listdir("./")

md_files = []
other_files = []
folders = []

for f in ls_dir:
    if f == send_dir or f[0] in "._":
        continue

    if os.path.isfile(f):
        if f[-3:] == ".md":
            md_files += [f]
        else:
            other_files += [f]
    else:
        folders += [f]
        ls_dir += [f + "/" + x for x in os.listdir(f"./{f}") if x[0] not in "._"]


for folder in folders:
    if not os.path.isdir(f"{send_dir}/{folder}"):
        os.makedirs(f"./{send_dir}/{folder}")

for file in md_files:
    # Set default title
    title = "Anna's Website"
    description = ""
    doc_type = "default"

    # Read file
    with open(file, "r") as f:
        lines = [l.strip() for l in f.readlines()]

    # Check for preamble
    preamble = [i for (i, x) in enumerate(lines) if x == "---"]

    if preamble != []:
        preamble_lines = lines[1:preamble[-1]]
        lines = lines[preamble[-1] + 1:]

        for line in preamble_lines:
            if line[:7] == "title: ":
                title = line[7:]

            if line[:13] == "description: ":
                description = line[13:]

            if line == "type: index":
                doc_type = "index"

    if doc_type == "index":
        with open(f"{send_dir}/{file[:-3]}.html", "w") as f:
            f.write("<head>\n")
            # Add in default header
            with open(f"_sections/preamble.html", "r") as s:
                content = s.readlines()

            [f.write(l) for l in content]

            f.write(f"<title>{title}</title>\n")
            f.write(f'<meta property="og:title" content="{title}">\n')
            f.write(f'<meta property="og:description" content="{description}">\n')
            f.write(f'<div style="display:none"><a rel="me" href="https://mathstodon.xyz/@awsloth">Mastodon</a></div>\n')
            f.write(f'<meta name="fediverse:creator" content="@awsloth@mathstodon.xyz">')
            f.write(f'<link rel="alternate" type="application/atom+xml" href="/feed.xml">')
            f.write("</head>\n")
            f.write("<body>\n")

            # Add in sidebar
            with open(f"_sections/sidebar.html", "r") as s:
                content = s.readlines()

            [f.write(l) for l in content]

            # Finish up
            f.write(markdowner.convert("\n".join(lines)).replace("<h1>", "<div class='block-title'>").replace("</h1>", "</div>"))
    else:
        with open(f"{send_dir}/{file[:-3]}.html", "w") as f:
            f.write("<head>\n")
            # Add in default header
            with open(f"_sections/preamble.html", "r") as s:
                content = s.readlines()

            [f.write(l) for l in content]

            f.write(f"<title>{title}</title>\n")
            f.write(f'<meta property="og:title" content="{title}">\n')
            f.write(f'<meta property="og:description" content="{description}">\n')
            f.write("</head>\n")
            f.write("<body>\n")

            # Add in sidebar
            with open(f"_sections/sidebar.html", "r") as s:
                content = s.readlines()

            [f.write(l) for l in content]

            # Add in default body
            with open(f"_sections/body.html", "r") as s:
                content = s.readlines()

            i = 0
            while (content[i] != "...\n"):
                f.write(content[i])
                i += 1

            i += 1

            # Finish up
            f.write(markdowner.convert("\n".join(lines)).replace("<h1>", "<div class='block-title'>").replace("</h1>", "</div>"))

            while i < len(content):
                f.write(content[i])
                i += 1

            f.write("</body>\n")

for file in other_files:
    shutil.copy2(file, f"{send_dir}/{file}")
